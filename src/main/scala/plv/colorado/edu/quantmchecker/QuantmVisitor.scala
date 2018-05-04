package plv.colorado.edu.quantmchecker

import javax.lang.model.element._

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
  private val DEBUG_WHICH_UNHANDLED_CASE = false
  private val ISSUE_ALL_UNANNOTATED_LISTS = true

  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val TOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])
  protected val BOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val SUMMARY: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Summary])

  private val NOT_SUPPORTED = "NOT SUPPORTED"
  private val MISS_CHANGES = "Expression might change variables appearing in lhs of an invariant, but the changes are not described by any invariant"
  private val BAD_LABEL = "Bad label"
  private val LIST_NOT_ANNOTATED = "List add found, but the receiver is not annotated"

  private val qualifierHierarchy = atypeFactory.getQualifierHierarchy

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }
  // val methodAnnotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala


  override def processClassTree(classTree: ClassTree): Unit = {
    val classType = TreeUtils.typeOf(classTree)
    val allFlds = ElementUtils.getAllFieldsIn(TreeUtils.elementFromDeclaration(classTree), elements).asScala
    if (classTree.getKind != Tree.Kind.ENUM) {
      allFlds.foreach { // Print recursive data types
        ve => if (ve.asType() == classType) Utils.logging("Recursive data type: " + classType.toString)
      }
    }
    super.processClassTree(classTree)
  }

  // User is responsible for encoding remainders into invariant.
  // Therefore, it does not matter if an expression does not change remainder.
  override def visitEnhancedForLoop(node: EnhancedForLoopTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)
        remainders.foreach {
          remainder =>
            // Remainder's name should be exactly the same as in invariant
            if (remainder == node.getExpression.toString) {
              if (!InvWithSolver.isValidAfterUpdate(invariant, (remainder, -1), ("", 0), updatedLabel, node))
                issueError(node, "")
            } else {
              // ignoreWarning(node, "[EnhancedForLoopTree] Not iterating over remainder is " + NOT_SUPPORTED)
            }
        }
    }
    super.visitEnhancedForLoop(node, p)
  }

  @deprecated
  private def getExprAnnotations(node: ExpressionTree): Option[AnnotationMirror] = {
    if (node == null) {
      None
    } else {
      /*val vtree = TreeUtils.enclosingVariable(atypeFactory.getPath(node))
      if (vtree == null)
        return List.empty
      val element = TreeUtils.elementFromDeclaration(vtree)*/
      val element = TreeUtils.elementFromUse(node)
      if (element == null) {
        None
      } else {
        // elements.getAllAnnotationMirrors(element).asScala.toList
        val annotations = atypeFactory.getAnnotatedType(element).getAnnotations
        Some(qualifierHierarchy.findAnnotationInHierarchy(annotations, qualifierHierarchy.getTopAnnotations.asScala.head))
        //element.getAnnotationMirrors.asScala.toList
      }
    }
  }

  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    val lhs = node.getVariable
    val lhsTyp = atypeFactory.getAnnotatedType(node.getVariable)
    val lhsAnno = lhsTyp.getAnnotations

    /**
      * Check if there is any destructive update (reassignment) that will invalidate an invariant
      * TODO: Currently if assignment invalidate any invariant, type check will fail
      * because we do not support destructively update either <remainder> or <self>
      * via any form of assignment
      */

    /**
      * TODO: Assume that any two variables won't have a same name. Otherwise,
      * if variable a is used in an invariant in one scope, but not used
      * in an invariant in the other scope, type check will fail.
      */
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)

        // Don't issue error if destructive update in class constructor
        val inConstructor = isInConstructor(node)
        // check if name of the expression is same as self or remainder
        remainders.foreach {
          remainder =>
            if (lhs.toString == remainder && inConstructor)
              issueError(node, "[AssignmentTree][Destructive update] is " + NOT_SUPPORTED)
        }
        selfs.foreach {
          self =>
            if (lhs.toString == self && inConstructor)
              issueError(node, "[AssignmentTree][Destructive update] is " + NOT_SUPPORTED)
        }
      // TODO: Otherwise, we assume lhs of assignment is side effect free
    }

    /**
      * This is unsound because of breaking subtype checking, but it is implemented for reducing annotation burden
      */
    if (avoidAssignSubtypeCheck(node.getExpression, lhsAnno.asScala.toSet)) {
      null
    } else {
      super.visitAssignment(node, p)
    }
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    val initializer = node.getInitializer
    if (initializer != null) {
      val lhsAnno = InvUtils.getAnnotationFromVariableTree(node, atypeFactory, trees)
      if (avoidAssignSubtypeCheck(node.getInitializer, lhsAnno))
        return null
    }
    super.visitVariable(node, p)
  }

  override def visitCompoundAssignment(node: CompoundAssignmentTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    // This expression could only change remainder
    (fieldInvs ++ localInvs).foreach {
      case invariant@Invariant(_, _, _, _) =>
        val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)
        remainders.foreach {
          remainder =>
            if (remainder == node.getVariable.toString) {
              node.getExpression match {
                case rhs: LiteralTree =>
                  rhs.getKind match {
                    case Tree.Kind.INT_LITERAL =>
                      val increment = rhs.getValue.asInstanceOf[Integer]
                      node.getKind match {
                        case Tree.Kind.PLUS_ASSIGNMENT | Tree.Kind.MINUS_ASSIGNMENT =>
                          if (!InvWithSolver.isValidAfterUpdate(invariant, (remainder, -increment), ("", 0), updatedLabel, node))
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
        }
      case _ => ignoreWarning(node, "[CompoundAssignmentTree] Malformed invariant is " + NOT_SUPPORTED); true
    }
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    val summaryExists = hasSummary(node)
    val inLoop = if (ISSUE_ALL_UNANNOTATED_LISTS) true else isInLoop(node)
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    // Check if side effects will invalidate invariants
    // TODO: o.f1().f2().f3(): methodinvocation (a.f().g()) -> memberselect (a.f())
    val callee: ExecutableElement = getMethodElementFromInvocation(node)
    val receiver: ExpressionTree = TreeUtils.getReceiverTree(node)
    val receiverName = if (receiver == null) "" else receiver.toString
    val receiverTyp: AnnotatedTypeMirror = getTypeFactory.getReceiverType(node)
    val receiverDecl: Element = {
      if (receiver != null) {
        TreeUtils.elementFromUse(receiver)
      } else { // this is member method invocation, therefore we return the class tree
        TreeUtils.elementFromDeclaration(getEnclosingClass(node))
      }
    }
    val receiverAnno: Option[AnnotationMirror] = getExprAnnotations(receiver)
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
          val whichVar = MethodSumUtils.whichVar(summary, callee)
          val numOfUpdatedInvs = (fieldInvs ++ localInvs).count {
            invariant =>
              val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)
              selfs.exists {
                self =>
                  if (whichVar.isLeft) { // Local variable is changed, according to method summary
                    val argIdx = whichVar.left.get
                    node.getArguments.get(argIdx) match {
                      case arg: IdentifierTree =>
                        if (arg.toString == self) { // Summary says: update self
                          if (!InvWithSolver.isValidAfterUpdate(invariant, ("", 0), (self, increment), updatedLabel, node))
                            issueError(node, "")
                          true
                        } else {
                          false
                        }
                      case _ =>
                        issueWarning(node, "[MethodInvocationTree] Complicated method arguments are " + NOT_SUPPORTED)
                        true
                    }
                  } else { // Field of the receiver should be updated, according to method summary
                    findFieldInClass(receiverTyp, whichVar.right.get) match {
                      case Some(field) =>
                        // If receiver is self and summary updates self's field
                        val updatedFldName = receiverName + "." + field.toString
                        if (updatedFldName == self) {
                          if (!InvWithSolver.isValidAfterUpdate(invariant, ("", 0), (self, increment), updatedLabel, node))
                            issueError(node, "")
                          true
                        } else {
                          false
                        }
                      case None =>
                        issueWarning(node, "Field not found. Probably a mistake in the summary: " + summary)
                        false
                    }
                  }
              }
          }
          // if (numOfUpdatedInvs == 0 && !summaryExists && inLoop)
            // issueWarning(node, LIST_NOT_ANNOTATED)
      }
    } else { // No method summaries found. Translate library methods (e.g. append, add) into numerical updates
      if (receiverTyp == null) { // Do nothing
      } else {
        val isColAdd = Utils.isCollectionAdd(types.erasure(receiverTyp.getUnderlyingType), callee)
        if (isColAdd) {
          // if (receiverAnno.isEmpty && inLoop) {
            // issueWarning(node, LIST_NOT_ANNOTATED)
          // }

          val numOfUpdatedInvs: Int = (fieldInvs ++ localInvs).count {
            invariant =>
              val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)
              selfs.exists {
                self =>
                  val selfCall = self + "." + callee.getSimpleName // E.g. x.f.g.add(1)
                  if (node.getMethodSelect.toString == selfCall) {
                    if (!InvWithSolver.isValidAfterUpdate(invariant, ("", 0), (self, 1), updatedLabel, node))
                      issueError(node, "")
                    true
                  } else {
                    false
                  }
              }
          }
          // if (numOfUpdatedInvs == 0 && !summaryExists && inLoop)
            // issueWarning(node, LIST_NOT_ANNOTATED)
        } else {
          // A method is invoked, but it does not have a summary and is not Collection ADD
        }
      }
    }
    super.visitMethodInvocation(node, p)
  }

  override def visitNewArray(node: NewArrayTree, p: Void): Void = {
    super.visitNewArray(node, p)
  }

  override def visitUnary(node: UnaryTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    (fieldInvs ++ localInvs).foreach {
      case invariant@Invariant(_, _, _, _) =>
        val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)
        remainders.foreach {
          remainder =>
            // This expression could only change remainder
            if (remainder == node.getExpression.toString) {
              node.getKind match {
                case Tree.Kind.POSTFIX_INCREMENT
                     | Tree.Kind.PREFIX_INCREMENT
                     | Tree.Kind.POSTFIX_DECREMENT
                     | Tree.Kind.PREFIX_DECREMENT =>
                  if (!InvWithSolver.isValidAfterUpdate(invariant, (remainder, -1), ("", 0), updatedLabel, node))
                    issueError(node, "")
                case _ => issueWarning(node, "[UnaryTree] Unknown unary operator is " + NOT_SUPPORTED); true
              }
            }
        }
      case _ => ignoreWarning(node, "[UnaryTree] " + NOT_SUPPORTED); true
    }
    super.visitUnary(node, p)
  }

  /**
    *
    * @param node           rhs of assignment
    * @param candidateAnnos annotations of lhs
    * @return Whether should we do subtype checking for assignments: lhs = rhs
    *         This is flow sensitive checking
    */
  private def avoidAssignSubtypeCheck(node: ExpressionTree, candidateAnnos: Set[AnnotationMirror]): Boolean = {
    if (candidateAnnos.isEmpty)
      return false
    val pickedAnno = qualifierHierarchy.findAnnotationInHierarchy(candidateAnnos.asJava, qualifierHierarchy.getTopAnnotations.asScala.head)
    node match {
      case t: NewClassTree =>
        // When it is an assignment (e.g. x = new C, where x has explicit annotation and C doesn't), don't type check.
        val rhsTyp = atypeFactory.getAnnotatedType(t)
        val rhsAnno = rhsTyp.getAnnotations
        // If rhs's annotation is empty or TOP
        if (rhsAnno == null
          || rhsAnno.isEmpty
          || AnnotationUtils.areSameIgnoringValues(rhsAnno.asScala.head, TOP)) {
          AnnotationUtils.areSameIgnoringValues(pickedAnno, INV)
        } else {
          false
        }
      case m: MethodInvocationTree =>
        // list = o.m(), where m's return value is annotated
        val callee: ExecutableElement = getMethodElementFromInvocation(m)
        val methodTree: MethodTree = trees.getTree(callee)
        if (methodTree == null || methodTree.getBody == null)
          return false
        val retAnno = callee.getReturnType.getAnnotationMirrors
        /*val stmts = methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
          (acc, stmt) => acc ++ flattenStmt(stmt)
        }
        val retAnnos = stmts.foldLeft(new HashSet[AnnotationMirror]) {
          (acc, s) =>
            s match {
              case s: ReturnTree =>
                if (s.getExpression != null) {
                  val anno = getExprAnnotations(s.getExpression) // atypeFactory.getAnnotatedType(s.getExpression)
                  acc ++ anno.filter(a => AnnotationUtils.areSameIgnoringValues(a, INV))
                } else {
                  acc
                }
              case _ => acc
            }
        }
        if (retAnnos.size == 1) {
          val isSubtype = atypeFactory.getQualifierHierarchy.isSubtype(retAnnos.head, pickedAnno)
          // if (!isSubtype)
          // println(node, retAnnos.head, pickedAnno)
          isSubtype
        } else {
          stmts.foreach {
            case s: ReturnTree =>
              if (s.getExpression != null) {
                val anno = getExprAnnotations(s.getExpression)
                // println(s.getExpression, anno, TreeUtils.elementFromUse(node) == null)
              }
            case _ =>
          }
          false
        }*/
        false
      case _ => false
    }
  }

  /**
    *
    * @param node a AST node
    * @return field invariants in the enclosing class
    *         local invariants in the enclosing method
    *         label of the enclosing statement
    */
  private def prepare(node: Tree): (Set[InvLangAST], Set[InvLangAST], String) = {
    val enclosingClass = getEnclosingClass(node)
    val enclosingMethod = getEnclosingMethod(node)
    val updatedLabel = getLabel(node)
    // if (enclosingClass == null || enclosingMethod == null)
      // Utils.logging("Empty enclosing class or method:\n" + node.toString)
    (
      if (enclosingClass == null) HashSet.empty else getClassFieldInvariants(enclosingClass).keySet,
      if (enclosingMethod == null) HashSet.empty else getLocalInvariants(enclosingMethod).keySet,
      updatedLabel
    )
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
          case member: VariableTree =>
            // Get annotations on class fields
            InvUtils.getAnnotationFromVariableTree(member, INV, atypeFactory, trees).foldLeft(acc) {
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
              // Local invariants should only be on variable declarations
              // Otherwise, invariants are simply ignored
              InvUtils.getAnnotationFromVariableTree(stmt, INV, atypeFactory, trees).foldLeft(acc) {
                case (acc2, a) => acc2 + (a -> methodTree)
              }
            case x@_ =>
              if (x.toString.contains("@Inv("))
                Utils.logging("Missed an invariant!\n" + x.toString)
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
  private def findFieldInClass(typ: AnnotatedTypeMirror, fieldName: String): Option[VariableElement] = {
    if (typ == null)
      return None
    val THIS = "this." // E.g. We want to look up a field named "chats", instead of "this.chats"
    val removeThis = if (fieldName.startsWith(THIS)) fieldName.substring(THIS.length) else fieldName
    Option(ElementUtils.findFieldInType(TypesUtils.getTypeElement(typ.getUnderlyingType), removeThis))
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
            // val variableName = summary.head
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

  @deprecated
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
    * @param fieldInv invariants on field declarations
    * @param localInv invariants on local variable declarations
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

  private def isInLoop(node: MethodInvocationTree): Boolean = {
    val path = atypeFactory.getPath(node).asScala
    path.exists {
      case t: EnhancedForLoopTree => true
      case t: ForLoopTree => true
      case t: WhileLoopTree => true
      case t: DoWhileLoopTree => true
      case _ => false
    }
  }

  /**
    *
    * @param node an AST node
    * @return if the enclosing method of the node has summary
    */
  private def hasSummary(node: Tree): Boolean = {
    val enclosingMethod = getEnclosingMethod(node)
    if (enclosingMethod != null) {
      val method: ExecutableElement = TreeUtils.elementFromDeclaration(enclosingMethod)
      val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY))
      summaries.nonEmpty
    } else {
      false
    }
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
