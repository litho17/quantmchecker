package plv.colorado.edu.quantmchecker

import java.io.File
import javax.lang.model.element._

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvTop, Summary}
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.SmtlibUtils

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
  // private val LIST_NOT_ANNOTATED = "List add found, but the receiver is not annotated"

  private val EMP_COLLECTION_PREFIX = "Collections.empty"

  private val qualifierHierarchy = atypeFactory.getQualifierHierarchy

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }

  override def visitMethod(node: MethodTree, p: Void): Void = {
    /*val obj = new Linear
    obj.add(1, "c62")
    obj.add(-1, "c63")
    obj.add(1, "c60")

    PrintStuff.printRedString(node.getName, SolveLP.optimizeWithinMethod(node, obj))*/
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

    /*Utils.COLLECTION_ADD.foreach {
    case (klass, method) =>
      types.asElement(types.erasure(lhsTyp.getUnderlyingType)) match {
        case te: TypeElement =>
          if (klass == te.getQualifiedName.toString) {
            Utils.logging("Destructive update: " + node.toString + "\n" + getEnclosingMethod(node))
          }
        case _ =>
      }
  }*/

    /**
      * Assume that any two variables won't have a same name. Otherwise,
      * if variable a is used in an invariant in one scope, but not used
      * in an invariant in the other scope, type check will fail.
      */
    (fieldInvs ++ localInvs).foreach {
      invariant =>
    }

    /**
      * This is unsound because of breaking subtype checking, but it is implemented for reducing annotation burden
      */
    if (avoidAssignSubtyCheck(node.getExpression)) {
      null
    } else {
      super.visitAssignment(node, p)
    }
  }

  override def visitCompoundAssignment(node: CompoundAssignmentTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    // This expression could only change remainder
    (fieldInvs ++ localInvs).foreach {
      /*case invariant@Invariant(_, _, _, _) =>
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
        }*/
      case _ => ignoreWarning(node, "[CompoundAssignmentTree] Malformed invariant"); true
    }
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    // val summaryExists = hasSummary(node)
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    // Check if side effects will invalidate invariants
    // TODO: methodinvocation (a.f().g()) -> memberselect (a.f())
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

    val callerSummary = Utils.getMethodSummary(getMethodElementFromDecl(getEnclosingMethod(node)), atypeFactory)
    val calleeSummary = Utils.getMethodSummary(getMethodElementFromInvocation(node), atypeFactory)
    if (calleeSummary.nonEmpty) {
      calleeSummary.foreach {
        summary =>
        /*val increment: Integer = summary match {
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
        }*/
        // if (numOfUpdatedInvs == 0 && !summaryExists && inLoop)
        // issueWarning(node, LIST_NOT_ANNOTATED)
      }
    } else { // No method summaries found. Translate library methods (e.g. append, add) into numerical updates
      if (receiverTyp == null) { // Do nothing
      } else {
        val absPath = root.getSourceFile.getName
        val relativePath = if (absPath.startsWith(Utils.DESKTOP_PATH + File.separator)) absPath.substring(Utils.DESKTOP_PATH.length + 1) else absPath

        val isColAdd = Utils.isColWhat("add", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
        val isIterNext = Utils.isColWhat("next", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
        val isColRem = Utils.isColWhat("remove", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
        if (isColRem)
          Utils.logging("list.remove: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)
        if (isColAdd) {
          // if (receiverAnno.isEmpty && inLoop) {
          // issueWarning(node, LIST_NOT_ANNOTATED)
          // }
          Utils.logging("list.add: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)

          /*val numOfUpdatedInvs: Int = (fieldInvs ++ localInvs).count {
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
          }*/
          // if (numOfUpdatedInvs == 0 && !summaryExists && inLoop)
          // issueWarning(node, LIST_NOT_ANNOTATED)
        }

        if (isIterNext) {
          /*val numOfUpdatedInvs: Int = (fieldInvs ++ localInvs).count {
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
          }*/
        }

        // A method is invoked, but it does not have a summary and is not Collection ADD
      }
    }
    super.visitMethodInvocation(node, p)
  }

  override def visitUnary(node: UnaryTree, p: Void): Void = {
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    (fieldInvs ++ localInvs).foreach {
      /*case invariant@Invariant(_, _, _, _) =>
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
        }*/
      case _ => ignoreWarning(node, "[UnaryTree] " + NOT_SUPPORTED); true
    }
    super.visitUnary(node, p)
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    // val lhsAnno = getAnnotationFromVariableTree(node, INV)
    if (avoidAssignSubtyCheck(node.getInitializer))
      return null
    super.visitVariable(node, p)
  }

  /**
    *
    * @param rhs rhs of assignment
    * @return Whether should we do subtype checking for assignments: lhs = rhs
    *         This is flow sensitive checking
    */
  private def avoidAssignSubtyCheck(rhs: ExpressionTree): Boolean = {
    if (rhs == null)
      return false
    val isDeclaration = {
      val element = TreeUtils.elementFromTree(rhs)
      val path = trees.getPath(element)
      if (path == null) false else TreeUtils.enclosingVariable(path) == null
    }
    if (isDeclaration)
      return true

    val rhsStr = rhs.toString
    rhs match {
      case t: NewClassTree => // E.g. x = new C(), where x has explicit annotation and C doesn't, don't type check.
        val rhsAnno = atypeFactory.getTypeAnnotation(t)
        rhsAnno == null || AnnotationUtils.areSameIgnoringValues(rhsAnno, TOP) // If rhs's annotation is empty or TOP
      case m: MethodInvocationTree =>
        val callee = getMethodElementFromInvocation(m)
        val receiver = TreeUtils.getReceiverTree(m)
        val receivetTyp = types.erasure(getTypeFactory.getReceiverType(m).getUnderlyingType)
        val isIter = Utils.isColWhat("iterator", receivetTyp, callee, atypeFactory) // E.g. it = x.iterator()
      val isClone = rhsStr == "clone"
        val isRhsEmp = rhsStr.startsWith(EMP_COLLECTION_PREFIX) // || rhsStr.startsWith("Collections.unmodifiable")
        if (isIter || isClone || isRhsEmp)
          return true
        false
      case _ =>
        val isRhsNull = rhsStr == "null"
        // val isInit = if (getEnclosingMethod(node) != null) getEnclosingMethod(node).toString.contains("init") else false
        isRhsNull // || isInit // unsound
    }
  }

  /**
    *
    * @param variable a variable
    * @param typCxt   a typing context
    * @return all types in the typing context that is dependent on the given variable
    */
  private def getVarType(variable: String, typCxt: HashMap[String, String]): HashSet[String] = {
    typCxt.foldLeft(new HashSet[String]) {
      case (acc, (v, typ)) => if (SmtlibUtils.containsToken(variable, typ)) acc + typ else acc
    }
  }

  private def getExprType(expr: ExpressionTree, typCxt: HashMap[String, String]): HashSet[String] = {
    ???
  }

  /**
    *
    * @param node a AST node
    * @return field invariants in the enclosing class
    *         local invariants in the enclosing method
    *         label of the enclosing statement
    */
  private def prepare(node: Tree): (HashMap[String, String], HashMap[String, String], String) = {
    val enclosingClass = getEnclosingClass(node)
    val enclosingMethod = getEnclosingMethod(node)
    val updatedLabel = getLabel(node)
    // if (enclosingClass == null || enclosingMethod == null)
    // Utils.logging("Empty enclosing class or method:\n" + node.toString)
    val fldInv = {
      if (enclosingClass == null) new HashMap[String, String]
      else atypeFactory.getFieldTypCxt(enclosingClass)
    }
    val localInv = {
      if (enclosingMethod == null) new HashMap[String, String]
      else atypeFactory.getLocalTypCxt(enclosingMethod)
    }
    (fldInv, localInv, updatedLabel)
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
