package plv.colorado.edu.quantmchecker

import java.io.File

import com.microsoft.z3.AST
import com.sun.source.tree._
import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu.quantmchecker.summarylang.{MSum, MSumI, MSumV, MethodSumUtils}
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.{CFRelation, SmtUtils, Z3Solver}
import plv.colorado.edu.{AccessPath, Utils, VarTyp}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUG_PATHS = false
  private val DEBUG_WHICH_UNHANDLED_CASE = false
  private val EMP_COLLECTION_PREFIX = "Collections.empty"

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }

  Utils.logging("# of verified methods, # of methods, # of queries, Z3 time")

  private var methodTrees = HashSet[MethodTree]()
  private var verifiedMethods = HashSet[MethodTree]()

  override def visitMethod(node: MethodTree, p: Void): Void = {
    methodTrees += node
    val localTypCxt = atypeFactory.getLocalTypCxt(node)
    val fldTypCxt = atypeFactory.getFieldTypCxt(getEnclosingClass(node))
    val typCxt = localTypCxt ++ fldTypCxt
    typCxt.foreach { // Check if each invariant is a valid SMTLIB2 string
      case (v, t) =>
        try {
          SmtUtils.parseSmtlibToToken(t.anno)
        }
        catch {
          case e: Exception => assert(false)
        }
    }
    typCxt.foreach { // T-Decl
      case (v, t) =>
        if (!t.isInput) {
          val init = initInv(t.anno, typCxt)
          typecheck(SmtUtils.mkAssertionForall(init), node, "T-Decl: " + v + ": " + t.anno)
        }
      case _ => true
    }
    if (node.getBody != null) { // Check if method's upper bound is less than Integer.MAX_VALUE
      val reachableListFlds = localTypCxt.foldLeft(new HashSet[AccessPath]) {
        case (acc, (v, t)) =>
          val cls = trees.getTree(t.getTypElement(types))
          acc ++ Utils.getReachableCollectionFields(cls, elements, types)
      }
      val sizes: Set[String] = localTypCxt.foldLeft(reachableListFlds.map { p => p.toString }) {
        case (acc, (v, t)) =>
          if (t.isInput) acc
          else {
            if (TypesUtils.isPrimitive(t.getTypElement(types).asType())) acc + "4"
            else acc + v
          }
      }
      val solver = new Z3Solver
      val cfRelation = new CFRelation(node.getBody, solver)
      val constraints: List[AST] = typCxt.foldLeft(new HashSet[String]) { // Collect constraints from types
        case (acc, (v, t)) => acc + t.anno
      }.map(s => Z3Solver.parseStrToZ3AST(s, solver)).toList
      val methodBody: AST = solver.mkEq(solver.getVar(Utils.hashCode(node.getBody)), solver.mkIntVal(1))
      val objective: AST = solver.mkAdd(sizes.map {
        size =>
          if (size.forall(_.isDigit)) solver.mkIntVal(size.toInt)
          else solver.getVar(size)
      }.toArray: _*)
      (methodBody :: cfRelation.constraints ::: constraints).foreach(s => solver.mkAssert(s))
      solver.mkAssert(solver.mkLe(objective, solver.mkIntVal(200)))
      // solver.optimize(objective.asInstanceOf[ArithExpr])
      val check = solver.checkSAT
      if (!check) {
        // Utils.logging("Typing context:\n" + typCxt)
        Utils.logging(SmtUtils.mkQueries(List("Assertions:\n", solver.getAssertions, SmtUtils.CHECK_SAT, SmtUtils.GET_OBJECTIVES, SmtUtils.GET_MODEL)))
        issueError(node, "Method has unbounded size!")
      } else {
        verifiedMethods += node
      }
    }
    super.visitMethod(node, p)
  }

  override def processClassTree(tree: ClassTree): Unit = {
    // Utils.logging("Field lists: " + atypeFactory.fieldLists.size + "\nLocal lists: " + atypeFactory.localLists.size)
    Utils.logging("Statistics: " + verifiedMethods.size + ", " + methodTrees.size + ", " + Z3Solver.TOTAL_QUERY + ", " + Z3Solver.TOTAL_TIME)
    super.processClassTree(tree)
  }

  private def typecheck(query: String, node: Tree, errorMsg: String): Boolean = {
    val ctx = Z3Solver.createContext
    val isChecked = Z3Solver.check(Z3Solver.parseSMTLIB2String(query, ctx), ctx)
    if (!isChecked) {
      // if (DEBUT_CHECK) println("\n-------\n" + query + "\n-------\n")
      Utils.logging("\n" + query + "\n")
      issueError(node, errorMsg)
    }
    isChecked
  }

  // Assume that all variables' scope is global to a method
  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    if (!isEnclosedInExprStmt(node)) // Here we handle x = v instead of T x = v
      return super.visitAssignment(node, p)

    val (fldTypCxt, localTypCxt, label) = prepare(node)
    val typCxt = fldTypCxt ++ localTypCxt
    val lhs = node.getVariable
    val rhs = node.getExpression
    // val lhsTyp = atypeFactory.getAnnotatedType(node.getVariable)
    // val lhsAnno = lhsTyp.getAnnotations
    typCxt.get(lhs.toString) match {
      case Some(lhsTyp) =>
        val lhsTypMirror = lhsTyp.getTypMirror(types)
        val lhsTypElement = lhsTyp.getTypElement(types)
        rhs match {
          case rhs: MethodInvocationTree => // z = x.iter and x = z.next
            val callSite = CallSite(rhs)
            val (callee, caller, callerName, callerTyp) =
              (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp)
            if (callerTyp == null) {
              if (avoidAssignSubtyCheck(lhsTyp.isInput, node.getExpression))
                return null
            } else {
              val isNext = Utils.isColWhat("next", types.erasure(callerTyp), callee, atypeFactory)
              val isIter = Utils.isColWhat("iterator", types.erasure(callerTyp), callee, atypeFactory)
              typCxt.foreach {
                case (v, t) =>
                  if (t.isInput) {
                    if (isNext) {
                      val newAnno = SmtUtils.substitute(t.anno, List(label, callerName),
                        List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkAdd(callerName, "1")))
                      val implication = SmtUtils.mkForallImply(t.anno, newAnno)
                      typecheck(implication, node, "x = z.next")
                    } else if (isIter) {
                      val newAnno = SmtUtils.substitute(t.anno, List(label, callerName),
                        List(SmtUtils.mkAdd(label, "1"), "0"))
                      val implication = SmtUtils.mkForallImply(t.anno, newAnno)
                      typecheck(implication, node, "z = x.iter")
                    } else {
                      val q = SmtUtils.substitute(t.anno, List(label), List(SmtUtils.mkAdd(label, "1")))
                      val implication = SmtUtils.mkForallImply(t.anno, q)
                      typecheck(implication, node, "x = m()")
                    }
                  }
              }
            }
          case rhs@(_: MemberSelectTree | _: IdentifierTree) =>
            if (TypesUtils.isPrimitive(lhsTypMirror)) { // Primitive types
              typCxt.foreach { // Must not create alias
                case (v, t) =>
                  if (t.isInput) {
                    val q = SmtUtils.substitute(t.anno,
                      List(label, lhs.toString),
                      List(SmtUtils.mkAdd(label, "1"), rhs.toString)
                    )
                    val implication = SmtUtils.mkForallImply(t.anno, q)
                    typecheck(implication, node, "x = y, x = y.f")
                  }
              }
            } else { // Class types
              // May create alias
              if (lhsTyp.anno != SmtUtils.ASSERT_FALSE) // Make the query fail
                issueError(node, "x = y, x = y.f: Annotation must be false")
            }
          case rhs@(_: BinaryTree | _: LiteralTree) => // Must not create alias
            typCxt.foreach {
              case (v, t) =>
                if (t.isInput) {
                  val q = SmtUtils.substitute(t.anno,
                    List(label, lhs.toString),
                    List(SmtUtils.mkAdd(label, "1"), rhs.toString)
                  )
                  val implication = SmtUtils.mkForallImply(t.anno, q)
                  typecheck(implication, node, "x = e_1 + e_2, x = n")
                }
            }
          case rhs: NewClassTree =>
            if (TypesUtils.isPrimitive(lhsTypMirror)) { // Primitive types
              typCxt.foreach { // Must not create alias
                case (v, t) =>
                  if (t.isInput) {
                    val q = SmtUtils.substitute(t.anno,
                      List(label),
                      List(SmtUtils.mkAdd(label, "1"))
                    )
                    val implication = SmtUtils.mkForallImply(t.anno, q)
                    typecheck(implication, node, "x = new Integer(?)")
                  }
              }
            } else { // Class types
              if (Utils.isCollectionTyp(lhsTypElement)) { // Must not create alias
                typCxt.foreach {
                  case (v, t) =>
                    if (t.isInput) {
                      val q = SmtUtils.substitute(t.anno,
                        List(label, lhs.toString),
                        List(SmtUtils.mkAdd(label, "1"), "0")
                      )
                      val implication = SmtUtils.mkForallImply(t.anno, q)
                      typecheck(implication, node, "x = new List")
                    }
                }
              } else { // Assume: class initializers are inlined; Must not create alias
                typCxt.foreach {
                  case (v, t) =>
                    if (t.isInput) {
                      val q = SmtUtils.substitute(t.anno,
                        List(label, lhs.toString),
                        List(SmtUtils.mkAdd(label, "1"), "0")
                      )
                      val implication = SmtUtils.mkForallImply(t.anno, q)
                      typecheck(implication, node, "x = new Class()")
                    }
                }
              }
            }
          case _ => // Do nothing
        }
      case None => // Do nothing
    }
    super.visitAssignment(node, p)
  }

  override def visitCompoundAssignment(node: CompoundAssignmentTree, p: Void): Void = {
    // case Tree.Kind.PLUS_ASSIGNMENT | Tree.Kind.MINUS_ASSIGNMENT =>
    super.visitCompoundAssignment(node, p)
  }

  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    if (!isEnclosedInExprStmt(node)) // Here we handle x.m() instead of x.m().n() (memberselect x.m())
      return super.visitMethodInvocation(node, p)

    val (fldTypCxt, localTypCxt, label) = prepare(node)
    val typCxt = fldTypCxt ++ localTypCxt
    val callSite = CallSite(node)
    val (callee, caller, callerName, callerTyp, vtPairs) =
      (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp, callSite.vtPairs)

    if (callerTyp != null) {
      val calleeSummary = getMethodSummaries(getMethodTypFromInvocation(node).getElement)
      val isAdd = Utils.isColWhat("add", types.erasure(callerTyp), callee, atypeFactory)
      val isRmv = Utils.isColWhat("remove", types.erasure(callerTyp), callee, atypeFactory)
      if (isAdd) Utils.logging("[list.add] line " + getLineNumber(node) + " " + node + "\n(" + getFileName + ")\n")
      typCxt.foreach { // Do not check iterator's and self's type annotation
        case (v, t) =>
          if (!t.isInput) {
            val (_old: List[String], _new: List[String]) = {
              if (isAdd) { // y.add(x)
                (List(label, callerName), List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkAdd(callerName, "1")))
              } else if (isRmv) { // y.rmv()
                (List(label, callerName), List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkSub(callerName, "1")))
              } else { // x.m(); Assume method body has already been inlined
                val (_o, _n) = getArgUpdates(calleeSummary, callerName)
                val o = label :: _o
                val n = SmtUtils.mkAdd(label, "1") :: _n
                (o, n)
              }
            }
            val q = SmtUtils.substitute(t.anno, _old, _new)
            val implication = SmtUtils.mkForallImply(t.anno, q)
            typecheck(implication, node, "y.add(x), y.rmv(), x.m()")
          }
      }
    }

    /**
      * @return List of variable names (we also support access path)
      *         and their corresponding new values after invoking the current method
      */
    def getArgUpdates(calleeSummary: HashSet[MSum], callerName: String): (List[String], List[String]) = {
      val UNKNOWN_VAL = Integer.MIN_VALUE
      val UNKNOWN = "unknown"
      val (arg, argUpdate) = calleeSummary.foldLeft(List[String](), List[String]()) {
        (acc, summary) =>
          val increment: Integer = summary match {
            case MSumI(_, i) => i
            case MSumV(name, i) => if (i == UNKNOWN) UNKNOWN_VAL else 0
          }
          val (idx, accessPath) = MethodSumUtils.whichVar(summary, callee)
          val target = {
            if (idx == -1) callerName
            else {
              node.getArguments.get(idx) match { // Assume all actual arguments are variables (i.e. have names)
                case arg: IdentifierTree =>
                  if (increment == UNKNOWN_VAL) {
                    typCxt.get(arg.toString) match {
                      case Some(argTyp) => if (argTyp.anno != SmtUtils.ASSERT_FALSE)
                        issueError(node, "x.m(): Annotation must be false")
                      case None => // ???
                    }
                  }
                  arg
                case _ => ""
              }
            }
          } + accessPath
          (target :: acc._1, SmtUtils.mkAdd(target, increment.toString) :: acc._2)
      }
      // if (calleeSummary.nonEmpty) println(arg, argUpdate, calleeSummary)
      (arg, argUpdate)
    }

    super.visitMethodInvocation(node, p)
  }

  override def visitUnary(node: UnaryTree, p: Void): Void = {
    /*Tree.Kind.POSTFIX_INCREMENT
                     | Tree.Kind.PREFIX_INCREMENT
                     | Tree.Kind.POSTFIX_DECREMENT
                     | Tree.Kind.PREFIX_DECREMENT
    */
    super.visitUnary(node, p)
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    if (avoidAssignSubtyCheck(atypeFactory.getVarAnnoMap(node).isInput, node.getInitializer))
      return null
    super.visitVariable(node, p)
  }

  /**
    *
    * @param rhs rhs of assignment
    * @return Whether should we do subtype checking for assignments: lhs = rhs
    *         This is flow sensitive checking
    */
  private def avoidAssignSubtyCheck(isInput: Boolean, rhs: ExpressionTree): Boolean = {
    if (isInput) return true // Don't do assignment check for Inputs
    if (rhs == null) return false

    val rhsStr = rhs.toString
    rhs match {
      case t: NewClassTree => // // x = new C, Must not create alias because we inline class initializers
        val rhsAnno = atypeFactory.getTypeAnnotation(t)
        if (rhsAnno == null || AnnotationUtils.areSameIgnoringValues(rhsAnno, atypeFactory.INVTOP)) // If rhs's annotation is empty or TOP
          return true
      case m: MethodInvocationTree => // x = m(), Must not create alias
        val callee = getMethodTypFromInvocation(m).getElement
        // val receiver = TreeUtils.getReceiverTree(m)
        val receiverTyp = getTypeFactory.getReceiverType(m)
        if (receiverTyp == null)
          return false
        val isIter = Utils.isColWhat("iterator", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
        val isClone = rhsStr == "clone"
        val isRhsEmp = rhsStr.startsWith(EMP_COLLECTION_PREFIX) // || rhsStr.startsWith("Collections.unmodifiable")
        if (isIter || isClone || isRhsEmp)
          return true
      case _ =>
        if (rhsStr == "null") return true
    }
    false
  }

  private def initInv(inv: String, typCxt: Map[String, VarTyp]): String = {
    val vars = SmtUtils.extractSyms(inv).filter {
      v =>
        typCxt.get(v) match {
          case Some(varTyp) => !varTyp.isInput
          case None => true
        }
    }.toList
    val _old = vars
    val _new = vars.map(_ => "0")
    SmtUtils.substitute(inv, _old, _new)
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
    * @param node a AST node
    * @return field invariants in the enclosing class
    *         local invariants in the enclosing method
    *         label of the enclosing statement
    */
  private def prepare(node: Tree): (Map[String, VarTyp], Map[String, VarTyp], String) = {
    val enclosingClass = getEnclosingClass(node)
    val enclosingMethod = getEnclosingMethod(node)
    val updatedLabel = getLabel(node)
    // if (enclosingClass == null || enclosingMethod == null)
    // Utils.logging("Empty enclosing class or method:\n" + node.toString)
    val fldInv = {
      if (enclosingClass == null) new HashMap[String, VarTyp]
      else atypeFactory.getFieldTypCxt(enclosingClass)
    }
    val localInv = {
      if (enclosingMethod == null) new HashMap[String, VarTyp]
      else atypeFactory.getLocalTypCxt(enclosingMethod)
    }
    (fldInv, localInv, updatedLabel)
  }

  private def getMethodTypFromInvocation(node: MethodInvocationTree): AnnotatedTypeMirror.AnnotatedExecutableType = atypeFactory.methodFromUse(node).methodType

  private def getMethodElementFromDecl(node: MethodTree): ExecutableElement = {
    if (node == null)
      return null
    TreeUtils.elementFromDeclaration(node)
  }

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

  private def getFileName: String = {
    val absPath = root.getSourceFile.getName
    if (absPath.startsWith(Utils.DESKTOP_PATH + File.separator)) absPath.substring(Utils.DESKTOP_PATH.length + 1) else absPath
  }

  /**
    *
    * @param method a method
    * @return the summary of the method
    */
  private def getMethodSummaries(method: ExecutableElement): HashSet[MSum] = {
    if (method == null)
      return new HashSet[MSum]
    val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, atypeFactory.SUMMARY)).toList
    val set = if (summaries.size == 1) {
      val summaryList = Utils.extractArrayValues(summaries.head, "value")
      if (summaryList.size % 2 != 0) {
        issueWarning(method, "Method summary should have even number of arguments")
        new HashSet[MSum]
      } else {
        summaryList.grouped(2).foldLeft(new HashSet[MSum]) {
          (acc, summary: List[String]) =>
            assert(summary.size == 2)
            // val variableName = summary.head
            if (summary(1).forall(c => c.isDigit)) {
              acc + MSumI(summary.head, Integer.parseInt(summary(1)))
            } else {
              acc + MSumV(summary.head, summary(1))
            }
        }
      }
    } else if (summaries.size > 1) {
      issueWarning(method, "Method should have exactly 1 summary")
      new HashSet[MSum]
    } else {
      new HashSet[MSum]
    }
    set
  }

  case class CallSite(node: MethodInvocationTree) {
    val callee: ExecutableElement = getMethodTypFromInvocation(node).getElement
    val caller: ExpressionTree = TreeUtils.getReceiverTree(node)
    val callerName: String = if (caller == null) "" else caller.toString
    val callerTyp: TypeMirror = callee.getReceiverType // getTypeFactory.getReceiverType(node)
    val vtPairs: List[(VariableElement, AnnotatedTypeMirror)] = callee.getParameters.asScala.zip(atypeFactory.fromElement(callee).getParameterTypes.asScala).toList
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
// elements.getAllAnnotationMirrors(receiverDecl).asScala.toList
// trees.getTypeMirror()
// atypeFactory.declarationFromElement(callee)
// val callerSummary = Utils.getMethodSummary(getMethodElementFromDecl(getEnclosingMethod(node)), atypeFactory)
// val calleeSummary = Utils.getMethodSummary(getMethodElementFromInvocation(node), atypeFactory)
// trees.getTree()
// trees.getPath()
// val lhsAnnotation = atypeFactory.getTypeAnnotation(atypeFactory.getAnnotatedTypeLhs(node).getAnnotations)
// types.asElement(TreeUtils.typeOf(variableTree))