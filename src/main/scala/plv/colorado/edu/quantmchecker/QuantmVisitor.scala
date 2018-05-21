package plv.colorado.edu.quantmchecker

import java.io.File
import javax.lang.model.element._

import com.sun.source.tree._
import net.sf.javailp.Linear
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.invlang._
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvTop, Summary}
import plv.colorado.edu.quantmchecker.summarylang.{MethodSumUtils, MethodSummary, MethodSummaryI, MethodSummaryV}
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.VerifyUtils

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
  // private val MISS_CHANGES = "Expression might change variables appearing in lhs of an invariant, but the changes are not described by any invariant"
  // private val LIST_NOT_ANNOTATED = "List add found, but the receiver is not annotated"

  private val EMP_COLLECTION_PREFIX = "Collections.empty"

  private val qualifierHierarchy = atypeFactory.getQualifierHierarchy

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }

  override def visitMethod(node: MethodTree, p: Void): Void = {
    val obj = new Linear
    obj.add(1, "c62")
    obj.add(-1, "c63")
    obj.add(1, "c60")

    PrintStuff.printRedString(node.getName, VerifyUtils.solve(node, obj))
    super.visitMethod(node, p)
  }

  override def processClassTree(classTree: ClassTree): Unit = {
    val classType = TreeUtils.typeOf(classTree)
    val allFlds: Iterable[VariableElement] = ElementUtils.getAllFieldsIn(TreeUtils.elementFromDeclaration(classTree), elements).asScala
    if (classTree.getKind != Tree.Kind.ENUM) {
      allFlds.foreach { // Print recursive data types
        ve =>
          if (ve.asType() == classType)
            Utils.logging("Recursive data type: " + classType.toString)
          // Print user defined classes with list field
          types.asElement(ve.asType()) match {
            case te: TypeElement =>
              val tree = trees.getTree(te)
              Utils.COLLECTION_ADD.foreach {
                case (klass, method) =>
                  if (klass == te.getQualifiedName.toString)
                    Utils.logging("Class with list field: " + classType)
              }
            case _ =>
          }
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
              if (!InvSolver.isValidAfterUpdate(invariant, (remainder, -1), ("", 0), updatedLabel, node))
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

    // Print destructive update to list field that are not in class constructors,
    // where the update is neither null or new class (because these two cases will
    // decrease memory usage and not lead to unsoundness if we only care over-approximation)
    if (lhs != null && TreeUtils.isFieldAccess(lhs) && !isInConstructor(node)) {
      val rhsStr = node.getExpression.toString
      val isRhsNull = rhsStr == "null"
      val isRhsNewClass = node.getExpression.isInstanceOf[NewClassTree]
      val isRhsEmp = rhsStr.startsWith(EMP_COLLECTION_PREFIX) // || rhsStr.startsWith("Collections.unmodifiable")
      val isInit = if (getEnclosingMethod(node) != null) getEnclosingMethod(node).toString.contains("init") else false
      val isClone = rhsStr == "clone"
      val dontCare = isRhsNull || isRhsNewClass || isRhsEmp || isInit || isClone
      Utils.COLLECTION_ADD.foreach {
        case (klass, method) =>
          types.asElement(types.erasure(lhsTyp.getUnderlyingType)) match {
            case te: TypeElement =>
              if (klass == te.getQualifiedName.toString && !dontCare) {
                Utils.logging("Destructive update: " + node.toString + "\n" + getEnclosingMethod(node))
              }
            case _ =>
          }
      }
    }

    /**
      * TODO: Assume that any two variables won't have a same name. Otherwise,
      * if variable a is used in an invariant in one scope, but not used
      * in an invariant in the other scope, type check will fail.
      */
    (fieldInvs ++ localInvs).foreach {
      invariant =>
        val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(invariant)

        // Don't issue error if destructive update is in class constructor
        val inConstructor = isInConstructor(node)
        // Don't issue error if destructive update is at declaration
        val isDeclaration = {
          val element = TreeUtils.elementFromTree(node)
          val path = trees.getPath(element)
          if (path == null)
            false
          else
            path.getLeaf.isInstanceOf[VariableTree]
        }

        /**
          * Check if there is any destructive update (reassignment) that will invalidate an invariant
          * Currently if assignment invalidate any invariant, type check will fail
          * because we do not support destructively update either <remainder> or <self>
          * via any form of assignment
          */
        remainders.foreach {
          remainder =>
            if (lhs.toString == remainder && !inConstructor && !isDeclaration)
              issueError(node, "[AssignmentTree][Destructive update] is " + NOT_SUPPORTED)
        }
        selfs.foreach {
          self =>
            if (lhs.toString == self && !inConstructor && !isDeclaration)
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
                          if (!InvSolver.isValidAfterUpdate(invariant, (remainder, -increment), ("", 0), updatedLabel, node))
                            issueError(node, "")
                        case _ => // All other compound assignments are not supported
                          issueWarning(node, "[CompoundAssignmentTree] Operator " + node.getKind + " is " + NOT_SUPPORTED)
                      }
                    case _ => issueWarning(node, "[CompoundAssignmentTree] Other literal kind is " + NOT_SUPPORTED); true
                  }
                case _ => issueWarning(node, "[CompoundAssignmentTree] Non-literal is " + NOT_SUPPORTED); true
              }
            } else {
              ignoreWarning(node, "[CompoundAssignmentTree] LHS is not remainder")
            }
        }
      case _ => ignoreWarning(node, "[CompoundAssignmentTree] Malformed invariant"); true
    }
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    // val summaryExists = hasSummary(node)
    // val inLoop = if (ISSUE_ALL_UNANNOTATED_LISTS) true else isInLoop(node)
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
    // elements.getAllAnnotationMirrors(receiverDecl).asScala.toList
    // trees.getTypeMirror()
    // atypeFactory.declarationFromElement(callee)

    val callerSummary = getMethodSummaries(getMethodElementFromDecl(getEnclosingMethod(node)))
    val calleeSummary = getMethodSummaries(getMethodElementFromInvocation(node))
    if (calleeSummary.nonEmpty) {
      calleeSummary.foreach {
        summary =>
          val increment: Integer = summary match {
            case MethodSummaryI(_, i) => i
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
                          if (!InvSolver.isValidAfterUpdate(invariant, ("", 0), (self, increment), updatedLabel, node))
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
                          if (!InvSolver.isValidAfterUpdate(invariant, ("", 0), (self, increment), updatedLabel, node))
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
        val absPath = root.getSourceFile.getName
        val relativePath = if (absPath.startsWith(Utils.DESKTOP_PATH + File.separator)) absPath.substring(Utils.DESKTOP_PATH.length + 1) else absPath

        val isColAdd = Utils.isCollectionAdd(types.erasure(receiverTyp.getUnderlyingType), callee)
        val isIterNext = Utils.isIterNext(types.erasure(receiverTyp.getUnderlyingType), callee)
        val isColRem = Utils.isCollectionRemove(types.erasure(receiverTyp.getUnderlyingType), callee)
        if (isColRem)
          Utils.logging("list.remove: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)
        if (isColAdd) {
          // if (receiverAnno.isEmpty && inLoop) {
          // issueWarning(node, LIST_NOT_ANNOTATED)
          // }
          Utils.logging("list.add: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)

          val numOfUpdatedInvs: Int = (fieldInvs ++ localInvs).count {
            invariant =>
              val (_, selfs: List[String]) = InvUtils.extractInv(invariant)
              selfs.exists {
                self =>
                  // If a Collection Add's effect is already described in summary,
                  // then there is no need to check if it will invalidate some invariant
                  val isDescribedInSummary = callerSummary.exists {
                    case MethodSummaryI(target, _) =>
                      if (target.contains(self)) true else false
                    case _ => false
                  }
                  val selfCall = self + "." + callee.getSimpleName // E.g. x.f.g.add(1)
                  if (node.getMethodSelect.toString == selfCall && !isDescribedInSummary) {
                    if (!InvSolver.isValidAfterUpdate(invariant, ("", 0), (self, 1), updatedLabel, node))
                      issueError(node, "")
                    true
                  } else {
                    false
                  }
              }
          }
          // if (numOfUpdatedInvs == 0 && !summaryExists && inLoop)
          // issueWarning(node, LIST_NOT_ANNOTATED)
        }

        if (isIterNext) {
          val numOfUpdatedInvs: Int = (fieldInvs ++ localInvs).count {
            invariant =>
              val (remainders: List[String], _) = InvUtils.extractInv(invariant)
              remainders.exists {
                remainder =>
                  val remainderCall = remainder + "." + callee.getSimpleName // E.g. x.f.g.add(1)
                  if (node.getMethodSelect.toString == remainderCall) {
                    if (!InvSolver.isValidAfterUpdate(invariant, (remainder, -1), ("", 0), updatedLabel, node))
                      issueError(node, "")
                    true
                  } else {
                    false
                  }
              }
          }
        }

        // A method is invoked, but it does not have a summary and is not Collection ADD
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
                  if (!InvSolver.isValidAfterUpdate(invariant, (remainder, -1), ("", 0), updatedLabel, node))
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
    node match {
      case t: NewClassTree => // When it is an assignment (e.g. x = new C, where x has explicit annotation and C doesn't), don't type check.
        val rhsAnno = atypeFactory.getTypeAnnotation(t)
        // If rhs's annotation is empty or TOP
        rhsAnno == null || AnnotationUtils.areSameIgnoringValues(rhsAnno, TOP)
      case m: MethodInvocationTree =>
        if (m.toString.startsWith(EMP_COLLECTION_PREFIX)) // E.g. List x = Collection.emptyList()
          return true

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
      case _ =>
        if (node.toString == "null") // if rhs is null
          true
        else
          false
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
    val fldInv = {
      if (enclosingClass == null)
        Set.empty.asInstanceOf[Set[InvLangAST]]
      else
        getClassFieldInvariants(enclosingClass).keySet
    }
    val localInv = {
      if (enclosingMethod == null)
        Set.empty.asInstanceOf[Set[InvLangAST]]
      else
        getLocalInvariants(enclosingMethod).keySet
    }
    (fldInv, localInv, updatedLabel)
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

  private def getMethodElementFromInvocation(node: MethodInvocationTree): ExecutableElement = {
    atypeFactory.methodFromUse(node).first.getElement
  }

  private def getMethodElementFromDecl(node: MethodTree): ExecutableElement = {
    if (node == null)
      return null
    TreeUtils.elementFromDeclaration(node)
  }

  /**
    *
    * @param typ       a class type
    * @param fieldName a field name
    * @return find the field in the class
    */
  private def findFieldInClass(typ: AnnotatedTypeMirror, fieldName: String): Option[VariableElement] = {
    def _findFldInCls(typ: TypeElement, fldName: List[String]): Option[VariableElement] = {
      if (fldName.isEmpty) {
        None
      } else {
        val f = ElementUtils.findFieldInType(typ, fldName.head)
        if (f == null) {
          None
        } else {
          if (fldName.tail.nonEmpty)
            _findFldInCls(TypesUtils.getTypeElement(f.asType()), fldName.tail)
          else
            Option(f)
        }
      }
    }

    if (typ == null)
      return None
    val names = fieldName.split("\\.").toList.filterNot(s => s == "this")
    _findFldInCls(TypesUtils.getTypeElement(typ.getUnderlyingType), names)
  }

  /**
    *
    * @param method a method
    * @return the summary of the method
    */
  private def getMethodSummaries(method: ExecutableElement): HashSet[MethodSummary] = {
    if (method == null)
      return new HashSet[MethodSummary]
    val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY)).toList
    if (summaries.size == 1) {
      val summaryList = Utils.extractArrayValues(summaries.head, "value")
      if (summaryList.size % 2 != 0) {
        issueWarning(method, "Method summary should have even number of arguments")
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
      issueWarning(method, "Method should have exactly 1 summary")
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
    // trees.getPath(root, node)
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
    * @return if it is in class constructor
    */
  private def isInConstructor(node: Tree): Boolean = {
    // val enclosingClass = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.CLASS).asInstanceOf[ClassTree]
    val enclosingMethod = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.METHOD).asInstanceOf[MethodTree]
    if (enclosingMethod == null)
      return false
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
