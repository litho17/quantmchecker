package plv.colorado.edu.quantmchecker

import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element.{AnnotationMirror, Element, ExecutableElement, VariableElement}

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.invlang._
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvTop, Summary}
import plv.colorado.edu.quantmchecker.summarylang.{MethodSumUtils, MethodSummary, MethodSummaryI, MethodSummaryV}
import plv.colorado.edu.quantmchecker.utils.PrintStuff

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUG_PATHS = false
  private val DEBUG_COLLECT_INV = false
  private val DEBUG_WHICH_UNHANDLED_CASE = false

  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val TOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])
  protected val BOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val SUMMARY: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Summary])

  private val NOT_SUPPORTED = "NOT SUPPORTED"
  private val MISS_CHANGES = "Expression might change variables appearing in lhs" +
    " of an invariant, but the changes are not described by any invariant"
  private val MALFORMAT_INVARIANT = "Malformatted invariant annotation"
  private val BAD_LABEL = "Bad label"
  private val LIST_NOT_ANNOTATED = "List add found, but the receiver is not annotated"

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }

  /**
    *
    * @param node
    * @param p
    * @return If a method has summary, then we skip it
    */
  override def visitMethod(node: MethodTree, p: Void): Void = {
    val method: ExecutableElement = TreeUtils.elementFromDeclaration(node)
    val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY))
    if (summaries.isEmpty)
      super.visitMethod(node, p)
    else
      null
  }

  /**
    * 1. Collect all invariants (from method bodies as well as from class fields)
    * 2. Collect all method summaries
    * 3. For every statement, check if any related invariant is preserved
    * 4. For every loop, check if any related invariant is preserved throughout the loop body
    * 5. For every branch, check if any related invariant is preserved throughout the branch body
    *
    * TO DO
    * 1. Override the methods that currently report type failures --- which is isSubType()
    * 2. Write annotations with ScalaZ3 and read them
    * 3. Connect upper bounds with callbacks' arguments via: method's return value is same size as method's argument
    * 4. INPUTINPUT is a special variable that represents input. On the line that decrements INPUTINPUT, do not report error even if not type check, because the decrement is meant to be non-deterministic.
    * 5. Annotate class fields
    */
  // val methodAnnotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala

  override def visitEnhancedForLoop(node: EnhancedForLoopTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = getPrepared(node)
    /**
      * Make sure ???
      */
    node.getExpression match {
      /**
        * This extension (handling EnhancedForLoopTree) makes the implementation context sensitive:
        * We have to know the expression is under which context, in order to apply proper updates
        */
      case expr: IdentifierTree =>
        (fieldInvs ++ localInvs).foreach {
          invariant =>
            val (remainder: String, self: List[String], fullSelf: String) = InvUtils.getRemSelf(invariant)
            if (remainder == expr.getName.toString) {
              if (!InvWithSolver.isValidAfterUpdate(invariant, -1, 0, updatedLabel, node))
                issueError(node, "")
            } else {
              ignoreWarning(node, "[EnhancedForLoopTree] Not iterating over remainder is not " + NOT_SUPPORTED)
              true
            }
        }
      case expr: MethodInvocationTree =>
        expr.getMethodSelect match {
          case mst: MemberSelectTree =>
            (fieldInvs ++ localInvs).foreach {
              invariant =>
                val (remainder: String, self: List[String], fullSelf: String) = InvUtils.getRemSelf(invariant)
                // Currently only support entrySet() in the header
                if (mst.getIdentifier.toString == "entrySet") {
                  if (mst.getExpression.toString == remainder) {
                    if (!InvWithSolver.isValidAfterUpdate(invariant, -1, 0, updatedLabel, node))
                      issueError(node, "")
                  } else {
                    ignoreWarning(node, "[EnhancedForLoopTree] Not iterating over remainder is not " + NOT_SUPPORTED)
                    true
                  }
                } else {
                  issueWarning(node, "[EnhancedForLoopTree] Not invoking entrySet is not " + NOT_SUPPORTED)
                  true
                }
            }
          case _ => issueWarning(node, "[EnhancedForLoopTree] " + NOT_SUPPORTED); true
        }
      case _ => issueWarning(node, "[EnhancedForLoopTree] " + NOT_SUPPORTED); true
    }
    super.visitEnhancedForLoop(node, p)
  }

  @deprecated
  private def getExprAnnotations(node: ExpressionTree): List[AnnotationMirror] = {
    if (node == null) {
      List.empty
    } else {
      val element = TreeUtils.elementFromUse(node)
      if (element == null)
        List.empty
      else
        element.getAnnotationMirrors.asScala.toList
    }
  }

  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = getPrepared(node)
    /**
      * Steps:
      * 1. Check subtyping
      * 2. Check if there is any destructive update (reassignment)
      */
    val lhs = node.getVariable
    val rhs = node.getExpression
    val lhsTyp = atypeFactory.getAnnotatedType(node.getVariable)
    val lhsAnno = lhsTyp.getAnnotations

    /**
      * Check if there is any destructive update (reassignment) that will invalidate an invariant
      * TODO: Currently assignment cannot invalidate any invariant
      * because we do not support changing either <remainder> or <self>
      * via any form of assignment
      */

    /**
      * TODO: Assume that any two variables won't have a same name. Otherwise,
      * if variable a is used in an invariant in one scope, but not used
      * in an invariant in the other scope, type check will fail.
      */
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        val (remainder, self) = invariant match {
          case Invariant(remainder, self, posLine, negLine) => (Some(remainder), Some(self))
          case InvNoRem(self, posLine, negLine) => (None, Some(self))
          case _ => issueWarning(node, "[AssignmentTree] " + NOT_SUPPORTED); (None, None)
        }

        /**
          *
          * @param name name of an expression
          * @return if the expression is same as self or remainder
          */
        def isReassign(name: String, self: String, remainder: Option[String]): Boolean = {
          val inConstructor = isInConstructor(node)
          if (name == self && !inConstructor) {
            // Don't issue error if in class constructor
            issueError(node, "[AssignmentTree][Destructive update] Reassigning <self> is " + NOT_SUPPORTED)
            false
          } else {
            remainder match {
              case Some(remainder) =>
                if (name == remainder && !inConstructor) {
                  // We require that remainder is always defined in current method scope
                  issueError(node, "[AssignmentTree][Destructive update] Reassigning remainder is " + NOT_SUPPORTED)
                  false
                } else {
                  true
                }
              case None => true
            }
          }
        }

        val lhsPreserveInv = self match {
          case Some(self) =>
            val _self = self.tail.foldLeft(self.head)((acc, e) => acc + "." + e)
            lhs match {
              case i: IdentifierTree => isReassign(i.getName.toString, _self, remainder)
              case s: MemberSelectTree =>
                if (s.toString == _self) {
                  issueError(node, "[AssignmentTree][Destructive update] Reassigning <self> is " + NOT_SUPPORTED)
                } else if (s.getExpression.toString == "this") {
                  isReassign(s.getIdentifier.toString, self.tail.foldLeft("")((acc, e) => acc + "." + e), remainder)
                }
              case _ => // TODO: Otherwise, we assume lhs of assignment is side effect free
            }
          case None =>
        }
    }

    val isAssignNew: Boolean = node.getExpression match {
      case t: NewClassTree =>
        val rhsTyp = atypeFactory.getAnnotatedType(t)
        val rhsAnno = rhsTyp.getAnnotations
        if (rhsAnno == null
          || rhsAnno.isEmpty
          || AnnotationUtils.areSameIgnoringValues(rhsAnno.asScala.head, TOP)) {
          lhsAnno != null && !lhsAnno.isEmpty && AnnotationUtils.areSameIgnoringValues(lhsAnno.asScala.head, INV)
        } else {
          false
        }
      case _ => false
    }

    /**
      * When it is an assignment (e.g. x = new C, where x has explicit annotation and C doesn't), don't type check.
      * This is unsound because breaking subtype checking, but it is implemented for reducing annotation burden
      */
    if (isAssignNew) {
      null
    } else {
      super.visitAssignment(node, p)
    }
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    val initializer = node.getInitializer
    if (initializer != null) {
      if (node.getModifiers.getAnnotations.asScala.isEmpty)
        super.visitVariable(node, p)
    }
    // When it is an assignment (e.g. x = new C, where x has explicit annotation and C doesn't), don't type check.
    null
  }

  override def visitCompoundAssignment(node: CompoundAssignmentTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = getPrepared(node)
    // This expression could only change remainder
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        invariant match {
          case Invariant(remainder, self, posLine, negLine) =>
            if (remainder == node.getVariable.toString) {
              node.getExpression match {
                case rhs: LiteralTree =>
                  rhs.getKind match {
                    case Tree.Kind.INT_LITERAL =>
                      val increment = rhs.getValue.asInstanceOf[Integer]
                      node.getKind match {
                        case Tree.Kind.PLUS_ASSIGNMENT | Tree.Kind.MINUS_ASSIGNMENT =>
                          if (!InvWithSolver.isValidAfterUpdate(invariant, -increment, 0, updatedLabel, node))
                            issueError(node, "")
                        case _ => // All other compound assignments are not supported
                          issueWarning(node, "[CompoundAssignmentTree] Operator " + node.getKind + " is " + NOT_SUPPORTED)
                      }
                    case _ => issueWarning(node, "[CompoundAssignmentTree] Other literal kind is " + NOT_SUPPORTED); true
                  }
                case _ => issueWarning(node, "[CompoundAssignmentTree] Non-literal is " + NOT_SUPPORTED); true
              }
            } else {
              ignoreWarning(node, "[CompoundAssignmentTree] LHS being not remainder " + NOT_SUPPORTED)
            }
          case _ => ignoreWarning(node, "[CompoundAssignmentTree] Malformed invariant is " + NOT_SUPPORTED); true
        }
    }
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = getPrepared(node)
    // Check if side effects will invalidate invariants
    // TODO: o.f1().f2().f3(): methodinvocation (a.f().g()) -> memberselect (a.f())
    val callee: ExecutableElement = getMethodElementFromInvocation(node)
    val receiver: ExpressionTree = TreeUtils.getReceiverTree(node)
    val receiverName = if (receiver == null) "" else receiver.toString + "."
    val receiverTyp: AnnotatedTypeMirror = getTypeFactory.getReceiverType(node)
    val receiverDecl: Element = {
      if (receiver != null) {
        TreeUtils.elementFromUse(receiver)
      } else { // this is member method invocation, therefore we return the class tree
        TreeUtils.elementFromDeclaration(getEnclosingClass(node))
      }
    }
    val receiverAnno: List[AnnotationMirror] = getExprAnnotations(receiver)
    // elements.getAllAnnotationMirrors(receiverDecl).asScala.toList
    // trees.getTypeMirror()
    // atypeFactory.declarationFromElement(callee)

    val summaries = getMethodSummaries(node)
    if (summaries.nonEmpty) {
      summaries.foreach {
        summary =>
          val increment: Integer = summary match {
            case MethodSummaryI(_, i) => i
            case MethodSummaryV(_, _) => 1
            // TODO: Not yet support describing changes via variable name in a method summary
            case _ => 0
          }

          /**
            * Method summary could either change <remainder> or <self>
            */
          val whichVar = MethodSumUtils.whichVar(summary, callee)
          (fieldInvs ++ localInvs).foreach {
            invariant =>
              val (remainder: String, self: List[String], fullSelf: String) = InvUtils.getRemSelf(invariant)

              if (whichVar.isLeft) { // Local variable is changed, according to method summary
                val argIdx = whichVar.left.get
                node.getArguments.get(argIdx) match {
                  case arg: IdentifierTree =>
                    if (arg.toString == remainder) { // Summary says: update remainder
                      if (!InvWithSolver.isValidAfterUpdate(invariant, -increment, 0, updatedLabel, node))
                        issueError(node, "")
                    } else if (arg.toString == fullSelf) { // Summary says: update self
                      if (!InvWithSolver.isValidAfterUpdate(invariant, 0, increment, updatedLabel, node))
                        issueError(node, "")
                    } else {
                      ignoreWarning(node, "[MethodInvocationTree] Method summary applies changes " +
                        "to a local variable, but that local variable is neither remainder or self " + (arg, remainder, self))
                    }
                  case _ =>
                    issueWarning(node, "[MethodInvocationTree] Complicated method arguments are " + NOT_SUPPORTED)
                }
              } else { // Field of the receiver should be updated, according to method summary
                findFieldInClass(receiverTyp.getUnderlyingType, whichVar.right.get) match {
                  case Some(field) =>
                    // If receiver is self and summary updates self's field
                    val updatedFldName = receiverName + field.toString
                    if (updatedFldName == fullSelf) {
                      if (!InvWithSolver.isValidAfterUpdate(invariant, 0, increment, updatedLabel, node))
                        issueError(node, "")
                    } else {
                      ignoreWarning(node, "Summary specifies a change in a field that is " +
                        "not described by invariant. " + (updatedFldName, fullSelf, summary, invariant))
                    }
                  case None =>
                    issueWarning(node, "Field not found. Probably a mistake in the summary: " + summary)
                }
              }
          }
      }
    } else {
      // No method summaries found
      // Translate library methods (e.g. append, add) into numerical updates
      if (receiverTyp == null) {
        // Might be invoking a super class
      } else {
        val isColAdd = Utils.isCollectionAdd(types.erasure(receiverTyp.getUnderlyingType), callee)
        if (isColAdd) {
          if (receiverAnno.isEmpty) {
            issueWarning(node, LIST_NOT_ANNOTATED)
          }

          (fieldInvs ++ localInvs).foreach {
            invariant =>
              val (remainder: String, self: List[String], fullSelf: String) = InvUtils.getRemSelf(invariant)
              val selfCall = fullSelf + "." + callee.getSimpleName // E.g. <self>.f.g.add(1)

              node.getMethodSelect match {
                case mst: MemberSelectTree =>
                  if (mst.getExpression.toString == remainder) {
                    // Remainder is changed [Although we don't expect this to happen]
                    // InvWithSolver.isValidAfterUpdate(invariant, -1, 0, lineNumber, expr)
                    issueWarning(node, "We don't expect Collection ADD to change remainder")
                  } else if (mst.toString == selfCall) {
                    // Self is changed, e.g. <self>.f.g.add(1)
                    InvWithSolver.isValidAfterUpdate(invariant, 0, 1, updatedLabel, node)
                  } else {
                    // This update does not influence the current invariant
                    ignoreWarning(node, "Collection ADD found, but the receiver is not annotated with invariant")
                  }
                case mst: IdentifierTree => // A member method is invoked, but it does not have a summary
                case _ => issueWarning(node, "[MethodInvocationTree] " + NOT_SUPPORTED); true
              }
          }
        } else {
          // TODO: might update remainder
          // A method is invoked, but it does not have a summary and is not Collection ADD
        }
      }
    }
    super.visitMethodInvocation(node, p)
  }

  override def visitNewArray(node: NewArrayTree, p: Void): Void = {
    // if (node.getInitializers != null) // Initializers are not supported
    // issueWarning(node, "[NewArrayTree] Initializers are " + NOT_SUPPORTED)
    super.visitNewArray(node, p)
  }

  override def visitUnary(node: UnaryTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = getPrepared(node)
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        invariant match {
          case Invariant(remainder, self, posLine, negLine) =>
            // This expression could only change remainder
            if (remainder == node.getExpression.toString) {
              node.getKind match {
                case Tree.Kind.POSTFIX_INCREMENT
                     | Tree.Kind.PREFIX_INCREMENT
                     | Tree.Kind.POSTFIX_DECREMENT
                     | Tree.Kind.PREFIX_DECREMENT =>
                  if (!InvWithSolver.isValidAfterUpdate(invariant, -1, 0, updatedLabel, node))
                    issueError(node, "")
                case _ => issueWarning(node, "[UnaryTree] Unknown unary operator is " + NOT_SUPPORTED); true
              }
            }
          case _ => ignoreWarning(node, "[UnaryTree] " + NOT_SUPPORTED); true
        }
    }
    super.visitUnary(node, p)
  }

  /**
    *
    * @param node
    * @return field invariants in the enclosing class
    *         local invariants in the enclosing method
    *         label of the enclosing statement
    */
  private def getPrepared(node: Tree): (Set[InvLangAST], Set[InvLangAST], String) = {
    val enclosingClass = getEnclosingClass(node)
    val enclosingMethod = getEnclosingMethod(node)
    assert(enclosingClass != null)
    assert(enclosingMethod != null)
    val fieldInvs = getClassFieldInvariants(enclosingClass)
    val localInvs = getLocalInvariants(enclosingMethod)
    val updatedLabel = getLabel(node)
    (fieldInvs.keySet, localInvs.keySet, updatedLabel)
  }

  /**
    *
    * @param classTree a class definition
    * @return a map from a line number to an invariant that might be changed by that line
    */
  private def getClassFieldInvariants(classTree: ClassTree): HashMap[InvLangAST, Tree] = {
    classTree.getMembers.asScala.foldLeft(new HashMap[InvLangAST, Tree]) {
      (acc, member) =>
        member match {
          case member: VariableTree => // Only care about variable declarations in a class
            /**
              * Get annotations on class fields
              */
            getAnnotationFromVariableTree(member, INV).foldLeft(acc) {
              case (acc2, a) => acc2 + (a -> classTree)
            }
          case _ => acc
        }
    }
  }

  /**
    *
    * @param methodTree a method
    * @return all invariants that are declared in the method
    */
  private def getLocalInvariants(methodTree: MethodTree): HashMap[InvLangAST, Tree] = {
    if (methodTree.getBody != null) {
      val stmts = methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ flattenStmt(stmt)
      } ++ methodTree.getParameters.asScala

      stmts.foldLeft(new HashMap[InvLangAST, Tree]) {
        (acc, stmt) =>
          stmt match {
            case stmt: VariableTree =>

              /**
                * Local invariants should only be on variable declarations
                * Otherwise, invariants are simply ignored
                */
              getAnnotationFromVariableTree(stmt, INV).foldLeft(acc) {
                case (acc2, a) => acc2 + (a -> methodTree)
              }
            case x@_ =>
              if (x.toString.contains("@Inv"))
                PrintStuff.printBlueString("Missed an invariant!", x, x.getClass)
              acc
          }
      }
    } else {
      new HashMap[InvLangAST, Tree]
    }
  }

  /**
    *
    * @param node a method invocation
    * @return the element of the callee
    */
  private def getMethodElementFromInvocation(node: MethodInvocationTree): ExecutableElement = {
    atypeFactory.methodFromUse(node).first.getElement
  }

  /**
    *
    * @param typ       a class type
    * @param fieldName a field name
    * @return find the field in the class
    */
  private def findFieldInClass(typ: TypeMirror, fieldName: String): Option[VariableElement] = {
    Option(ElementUtils.findFieldInType(TypesUtils.getTypeElement(typ), fieldName))
  }

  /**
    *
    * @param node a method invocation tree
    * @return the summary of the invoked method
    */
  private def getMethodSummaries(node: MethodInvocationTree): HashSet[MethodSummary] = {
    val invokedMethod: ExecutableElement = getMethodElementFromInvocation(node)
    val summaries = atypeFactory.getDeclAnnotations(invokedMethod).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY)).toList
    if (summaries.size == 1) {
      val summaryList = Utils.extractValues(summaries.head)
      if (summaryList.size % 2 != 0) {
        issueWarning(invokedMethod, "Method summary should have even number of arguments")
        new HashSet[MethodSummary]
      } else {
        summaryList.grouped(2).foldLeft(new HashSet[MethodSummary]) {
          (acc, summary) =>
            assert(summary.size == 2)
            val variableName = summary.head
            if (summary(1).forall(c => c.isDigit)) {
              acc + MethodSummaryI(summaryList.head, Integer.parseInt(summaryList(1)))
            } else {
              acc + MethodSummaryV(summaryList.head, summaryList(1))
            }
        }
      }
    } else if (summaries.size > 1) {
      issueWarning(invokedMethod, "Method should have exactly 1 summary")
      new HashSet[MethodSummary]
    } else {
      new HashSet[MethodSummary]
    }
  }

  /**
    *
    * @param node a statement tree
    * @return collect a set of all leave statements
    *         Note: All other StatementTrees are ignored
    */
  private def flattenStmt(node: StatementTree): HashSet[StatementTree] = {
    node match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(new HashSet[StatementTree])((acc, s) => acc ++ flattenStmt(s))
      case stmt: DoWhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: EnhancedForLoopTree => flattenStmt(stmt.getStatement)
      case stmt: ForLoopTree =>
        stmt.getInitializer.asScala.foldLeft(flattenStmt(stmt.getStatement)) {
          (acc, s) => acc ++ flattenStmt(s)
        }
      case stmt: WhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: LabeledStatementTree => flattenStmt(stmt.getStatement)
      case stmt: IfTree => flattenStmt(stmt.getThenStatement) ++ flattenStmt(stmt.getElseStatement)
      case stmt: SwitchTree =>
        stmt.getCases.asScala.foldLeft(new HashSet[StatementTree]) {
          (acc, caseTree) => caseTree.getStatements.asScala.foldLeft(acc)((acc2, s) => acc2 ++ flattenStmt(s))
        }
      case stmt: ExpressionStatementTree => HashSet[StatementTree](stmt)
      case stmt: ReturnTree => HashSet[StatementTree](stmt)
      case stmt: VariableTree => HashSet[StatementTree](stmt)
      case stmt: TryTree => flattenStmt(stmt.getBlock) ++ flattenStmt(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => flattenStmt(stmt.getBlock)
      case _ => new HashSet[StatementTree]
    }
  }

  /**
    *
    * @param node a statement
    * @return line number of the statement
    */
  private def getLineNumber(node: Tree): Int = {
    val line_long = Utils.getLineNumber(node, positions, root)
    assert(line_long <= Integer.MAX_VALUE, "line number overflows")
    line_long.toInt
  }

  private def ignoreWarning(node: Object, msg: String): Unit = {
    // checker.report(Result.warning(msg), node)
  }

  private def issueWarning(node: Object, msg: String): Unit = {
    // Debug only: I want to know which unhandled case issues the warning
    if (DEBUG_WHICH_UNHANDLED_CASE) {
      val trace = Thread.currentThread().getStackTrace.toList.filter(s => s.toString.contains("QuantmVisitor.scala"))(1)
      PrintStuff.printGreenString("WARNING issued by " + trace.getFileName + ": " + trace.getLineNumber)
    }
    checker.report(Result.warning(msg), node)
  }

  private def issueError(node: Object, msg: String): Unit = {
    checker.report(Result.failure(msg), node)
  }

  /**
    *
    * @param node  a variable tree
    * @param annot which annotation to collect
    * @return collect the specified type of annotations in the variable tree
    */
  private def getAnnotationFromVariableTree(node: VariableTree, annot: AnnotationMirror): HashSet[InvLangAST] = {
    val annotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala
    /**
      * Extract annotations of Inv type
      */
    val listInvAnnotations = annotations.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, annot))
    // val annotations: List[String] = AnnoTypeUtils.extractValues(TreeUtils.annotationFromAnnotationTree(node))
    if (listInvAnnotations.nonEmpty) {
      if (DEBUG_COLLECT_INV) println(listInvAnnotations)
      val invs: List[String] = Utils.extractValues(listInvAnnotations.head)
      // assert(invs.size == 1, "Inv should only have 1 element")
      invs.foldLeft(new HashSet[InvLangAST]) {
        (acc, str) =>
          // TODO: Before parsing, replace multiple spaces with a single space
          val invStr = str.replaceAll("\\s+", " ")
          val inv = InvLangCompiler(invStr)
          if (inv.isRight) {
            val name = node.getName.toString // the variable that <self> represents
            inv.right.get match {
              case Invariant(remainder, self, posLine, negLine) =>
                val invariant = Invariant(remainder, name :: self, posLine, negLine)
                if (invariant.toString != invStr) {
                  issueError(node, MALFORMAT_INVARIANT)
                  acc // parser error
                } else {
                  acc + invariant
                }
              case InvNoRem(self, posLine, negLine) =>
                val invariant = InvNoRem(name :: self, posLine, negLine)
                if (invariant.toString != invStr) {
                  issueError(node, MALFORMAT_INVARIANT)
                  acc // parser error
                } else {
                  acc + invariant
                }
              case _ => issueError(node, MALFORMAT_INVARIANT); acc
            }
          } else {
            issueError(node, MALFORMAT_INVARIANT)
            acc // parser error
          }
      }
    } else {
      new HashSet[InvLangAST]
    }
  }

  private def getEnclosingClass(node: Tree): ClassTree = TreeUtils.enclosingClass(atypeFactory.getPath(node))

  private def getEnclosingMethod(node: Tree): MethodTree = TreeUtils.enclosingMethod(atypeFactory.getPath(node))

  /**
    *
    * @param node a statement or expression
    * @return label of the enclosing statement of node, if any
    */
  private def getLabel(node: Tree): String = {
    val enclosingLabel = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.LABELED_STATEMENT).asInstanceOf[LabeledStatementTree]
    if (enclosingLabel != null) {
      enclosingLabel.getLabel.toString
    } else {
      ""
    }
  }

  /**
    *
    * @param node a statement or expression
    * @param fieldInv
    * @param localInv
    * @return all invariants in the enclosing method and class
    *         Resolve naming conflict for variables between local and field
    */
  private def getRelevantInv(node: Tree,
                             fieldInv: HashMap[InvLangAST, Tree],
                             localInv: HashMap[InvLangAST, Tree]): HashSet[InvLangAST] = {
    val enclosingClass = getEnclosingClass(node)
    val enclosingMethod = getEnclosingMethod(node)
    val field = fieldInv.filter { case (i, t) => t == enclosingClass }.keySet
    val local = localInv.filter { case (i, t) => t == enclosingMethod }.keySet
    new HashSet ++ field ++ local
  }

  /**
    *
    * @param node a statement or expression
    * @return if it is in class constructor
    */
  private def isInConstructor(node: Tree): Boolean = {
    // val enclosingClass = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.CLASS).asInstanceOf[ClassTree]
    val enclosingMethod = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.METHOD).asInstanceOf[MethodTree]
    enclosingMethod.getName.toString == "<init>"
  }

  @deprecated
  private def getTypeQualifiers: HashSet[AnnotationMirror] = new HashSet[AnnotationMirror] ++ atypeFactory.getQualifierHierarchy.getTypeQualifiers.asScala

  @deprecated
  private def getAnnotationMirror(node: Tree): HashSet[AnnotationMirror] = new HashSet() ++ atypeFactory.getAnnotatedType(node).getAnnotations.asScala

  /** Places to look for help:
    * 1. TreeUtils.xxx
    * TreeUtils.elementFromTree(node)
    * val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(atypeFactory.getPath(node))
    * 2. this.checker.xxx
    * 3. atypeFactory.xxx
    * 4. elements.xxx
    * 5. trees.xxx
    * 6. types.xxx
    */
}
