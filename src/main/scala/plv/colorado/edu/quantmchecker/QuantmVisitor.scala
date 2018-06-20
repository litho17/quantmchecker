package plv.colorado.edu.quantmchecker

import java.io.File
import javax.lang.model.element._

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual._
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.{SmtUtils, Z3Solver}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUT_CHECK = true
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

  // Assume that all variables' scope is global to a method
  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    if (!isEnclosedInExprStmt(node))
      return super.visitAssignment(node, p)

    val (fieldInvs, localInvs, label) = prepare(node)
    val lhs = node.getVariable
    val rhs = node.getExpression
    // val lhsTyp = atypeFactory.getAnnotatedType(node.getVariable)
    // val lhsAnno = lhsTyp.getAnnotations
    val lhsTyp = inferVarType(node.getVariable.toString, fieldInvs ++ localInvs) // Invariant: lhs is replaced with self
    val rhsTyp = { // Invariant: lhs is replaced with self
      val set = inferExprType(node.getExpression, fieldInvs ++ localInvs)
      if (set.nonEmpty) set + SmtUtils.mkEq(Utils.hashCode(rhs), SmtUtils.SELF) else set
    }.map{ s => SmtUtils.substitute(s, List(label, lhs.toString), List(SmtUtils.mkAdd(label, "1"), SmtUtils.SELF)) }

    rhs match {
      case rhs: MethodInvocationTree =>
        val callSite = CallSite(rhs)
        val (callee, caller, callerName, callerTyp) =
          (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp)
        if (callerTyp != null) {
          val isNext = Utils.isColWhat("next", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)
          val isRmv = Utils.isColWhat("remove", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)
          (fieldInvs ++ localInvs).foreach {
            case (v, t) =>
              if (isRmv) {
              }
              if (isNext) {
                val p = t
                val q = SmtUtils.substitute(p, List(label, callerName),
                  List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkSub(callerName, "1")))
                val implication = SmtUtils.mkImply(p, q)
                if (!Z3Solver.check(Z3Solver.parseSMTLIB2String(implication))) {
                  if (DEBUT_CHECK) println(implication)
                  issueWarning(node, "list.next: invariant broken")
                }
              }
          }
        }
      case _ =>
        val implication = SmtUtils.mkImply(SmtUtils.conjunctionAll(rhsTyp), SmtUtils.conjunctionAll(lhsTyp))
        if (!Z3Solver.check(Z3Solver.parseSMTLIB2String(implication))) {
          if (DEBUT_CHECK) println(implication)
          issueError(node, "In assignment: rhs's type doesn't imply lhs's")
        }
        // types.asElement(types.erasure(lhsTyp.getUnderlyingType))

        (fieldInvs ++ localInvs).foreach {
          case (v, inv) =>
            if (!atypeFactory.isDependentOn(lhs.toString, inv)) {
              val q = SmtUtils.substitute(inv, List(label), List(SmtUtils.mkAdd(label, "1")))
              val implication = SmtUtils.mkImply(inv, q)
              if (!Z3Solver.check(Z3Solver.parseSMTLIB2String(implication))) {
                if (DEBUT_CHECK) println(implication)
                issueError(node, "In assignment: invariant invalidated due to counter increment")
              }
            }
        }
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
    // case Tree.Kind.PLUS_ASSIGNMENT | Tree.Kind.MINUS_ASSIGNMENT =>
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    if (!isEnclosedInExprStmt(node))
      return super.visitMethodInvocation(node, p)

    val (fieldInvs, localInvs, label) = prepare(node)
    // TODO: methodinvocation (a.f().g()) -> memberselect (a.f())
    val callSite = CallSite(node)
    val (callee, caller, callerName, callerTyp, callerDecl, vtPairs) =
      (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp, callSite.callerDecl, callSite.vtPairs)

    if (callerTyp != null) {
      val absPath = root.getSourceFile.getName
      val relativePath = if (absPath.startsWith(Utils.DESKTOP_PATH + File.separator)) absPath.substring(Utils.DESKTOP_PATH.length + 1) else absPath

      vtPairs.foldLeft(new HashSet[String]) {
        case (acc, (v, t: AnnotatedTypeMirror)) =>
          val anno = atypeFactory.getTypeAnnotation(t.getAnnotations)
          if (anno != null) {
            val map = atypeFactory.getVarAnnoMap(anno)
            acc
          } else acc
      }

      val isAdd = Utils.isColWhat("add", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)

      // Utils.logging("list.remove: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)
      // Utils.logging("list.add: [Line " + getLineNumber(node) + "] " + relativePath + ", " + node.toString)
      (fieldInvs ++ localInvs).filter { case (v, t) => !v.startsWith(callerName) }.foreach {
        case (v: String, t: String) => // E.g. v.add1() affects v.f1's length
          if (isAdd) {
            // issueWarning(node, LIST_NOT_ANNOTATED)
          }
      }

      // A method is invoked, but it does not have a summary and is not Collection ADD
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
    * @param expr an expression
    * @return if the expression is a direct subtree of an expression statement
    */
  private def isEnclosedInExprStmt(expr: ExpressionTree): Boolean = {
    val exprStmt = TreeUtils.enclosingOfKind(atypeFactory.getPath(expr), Tree.Kind.EXPRESSION_STATEMENT)
    if (exprStmt == null) false
    else exprStmt.asInstanceOf[ExpressionStatementTree].getExpression == expr
  }

  /**
    *
    * @param v      name of a variable
    * @param typCxt a typing context
    * @return all types in the typing context that is dependent on
    *         the given variable name (e.g. v -> {inv1,inv2}/v.f -> {inv3,inv4})
    */
  private def inferVarType(v: String, typCxt: Map[String, String]): HashSet[String] = {
    val selfTyp: HashSet[String] = typCxt.get(v) match {
      case Some(s) => HashSet(s)
      case None => HashSet.empty
    }
    val dependentTyp = typCxt.foldLeft(new HashSet[String]) {
      case (acc2, (vInEnv, typInEnv)) =>
        if (SmtUtils.containsToken(typInEnv, v))
          acc2 + SmtUtils.substitute(typInEnv, List(SmtUtils.SELF), List(vInEnv)) // E.g. self -> vInEnv
        else acc2
    }
    // Check separately for the case where v does not have any type annotation
    if (dependentTyp.isEmpty && selfTyp.isEmpty) HashSet.empty
    else (selfTyp ++ dependentTyp).map(s => SmtUtils.substitute(s, List(v), List(SmtUtils.SELF)))
  }

  /**
    *
    * @param expr   an expression
    * @param typCxt a typing context
    * @return type constraints on the expression
    */
  private def inferExprType(expr: ExpressionTree, typCxt: Map[String, String]): HashSet[String] = {
    expr match {
      case e: MemberSelectTree => inferVarType(e.toString, typCxt) // E.g. v.f
      case e: IdentifierTree => inferVarType(e.toString, typCxt)
      case e: LiteralTree =>
        e.getKind match {
          case Tree.Kind.INT_LITERAL =>
            // To make it consistent that, it means cannot infer a type when returning an empty set
            HashSet[String](SmtUtils.mkEq(e.toString, e.toString))
          case _ => new HashSet[String] // ignored
        }
      case e: BinaryTree =>
        val left = e.getLeftOperand.toString
        val right = e.getRightOperand.toString
        val leftCons = inferExprType(e.getLeftOperand, typCxt)
        val rightCons = inferExprType(e.getRightOperand, typCxt)
        val eq = e.getKind match {
          case Tree.Kind.PLUS => SmtUtils.mkEq(Utils.hashCode(e), SmtUtils.mkAdd(left, right))
          case Tree.Kind.MINUS => SmtUtils.mkEq(Utils.hashCode(e), SmtUtils.mkSub(left, right))
          case _ => "" // ignored
        }
        // If cannot infer constraints for any operand, then cannot infer constraints for the binary expression
        if (leftCons.nonEmpty && rightCons.nonEmpty && eq != "") leftCons ++ rightCons + eq else new HashSet[String]
      // case e: MethodInvocationTree =>
      case _ => new HashSet[String] // ignored
    }
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
    * @return label of the immediate enclosing expression statement of the node, if any
    */
  private def getLabel(node: Tree): String = {
    // trees.getPath(root, node)
    val enclosingLabel = TreeUtils.enclosingOfKind(atypeFactory.getPath(node), Tree.Kind.LABELED_STATEMENT).asInstanceOf[LabeledStatementTree]
    if (enclosingLabel != null) {
      if (enclosingLabel.getStatement.isInstanceOf[ExpressionStatementTree]) enclosingLabel.getLabel.toString else ""
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

  case class CallSite(node: MethodInvocationTree) {
    val callee: ExecutableElement = getMethodElementFromInvocation(node)
    val caller: ExpressionTree = TreeUtils.getReceiverTree(node)
    val callerName: String = if (caller == null) "" else caller.toString
    val callerTyp: AnnotatedTypeMirror = getTypeFactory.getReceiverType(node)
    val callerDecl: Element = {
      if (caller != null) {
        TreeUtils.elementFromUse(caller)
      } else { // this is member method invocation, therefore we return the class tree
        TreeUtils.elementFromDeclaration(getEnclosingClass(node))
      }
    }
    val vtPairs: List[(VariableElement, AnnotatedTypeMirror)] = callee.getParameters.asScala.zip(atypeFactory.fromElement(callee).getParameterTypes.asScala).toList
    // elements.getAllAnnotationMirrors(receiverDecl).asScala.toList
    // trees.getTypeMirror()
    // atypeFactory.declarationFromElement(callee)
    // val callerSummary = Utils.getMethodSummary(getMethodElementFromDecl(getEnclosingMethod(node)), atypeFactory)
    // val calleeSummary = Utils.getMethodSummary(getMethodElementFromInvocation(node), atypeFactory)
  }

}
