package plv.colorado.edu.quantmchecker

import java.io.File

import com.sun.source.tree._
import javax.lang.model.element._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil._
import plv.colorado.edu._
import plv.colorado.edu.quantmchecker.summarylang.{MSum, MSumI, MSumV, MethodSumUtils}
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.{CFRelation, SmtUtils, Z3Solver}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUG = true
  private val DEBUG_PATHS = false
  private val DEBUG_WHICH_UNHANDLED_CASE = false
  private val EMP_COLLECTION_PREFIX = "Collections.empty"
  private val SIZE_BOUND = 1000

  if (DEBUG_PATHS) {
    PrintStuff.printRedString("java.class.path: " + System.getProperty("java.class.path"))
    PrintStuff.printRedString("java.library.path: " + System.getProperty("java.library.path"))
  }

  Utils.logging("# of verified methods, # of methods, # of queries, Z3 time")

  private var methodTrees = new HashSet[MethodTree]
  private var verifiedMethods = new HashSet[MethodTree]
  private var failCauses = new HashSet[FailCause]
  // private var localCollections = new HashSet[VarTyp]

  override def visitMethod(node: MethodTree, p: Void): Void = {
    methodTrees += node
    val localTypCxt = atypeFactory.getLocalTypCxt(node, false)
    val localTypCxtWithParameters = atypeFactory.getLocalTypCxt(node, true)
    val fldTypCxt = atypeFactory.getFieldTypCxt(TreeUtils.enclosingClass(atypeFactory.getPath(node)))
    val typCxt = localTypCxtWithParameters ++ fldTypCxt
    typCxt.cxt.foreach { // Check if each invariant is a valid SMTLIB2 string
      t => SmtUtils.parseSmtlibToToken(t.anno)
    }
    localTypCxt.cxt.foreach { // T-Decl
      t =>
        if (!t.isInput) {
          val init = initInv(t.anno, typCxt, node)
          typecheck(SmtUtils.mkAssertionForall(init), node, "T-Decl: " + t.anno)
        }
    }
    val isBounded = {
      if (node.getBody != null) { // Check if method's total variable size is less than SIZE_BOUND
        val sizes: Set[String] = localTypCxt.cxt.foldLeft(new HashSet[String]) {
          case (acc, t) =>
            if (!t.isInput) {
              val cls = trees.getTree(t.getTypElement(types))
              if (TypesUtils.isPrimitive(t.getTypMirror)) acc + "4"
              else { // Class type
                val varName = t.varElement.getSimpleName.toString
                if (Utils.isCollectionTyp(t.getTypElement(types))) acc + varName
                else {
                  val res = Utils.getReachableSize(cls, elements, types, trees, varName)
                  // Utils.logging(v + "\n" + res.toString() + "\n")
                  acc ++ res
                }
              }
            } else acc
        }
        val cfRelation = new CFRelation(node.getBody, new Z3Solver).constraints.map(ast => ast.toString).toArray
        val methodBodyCounter = SmtUtils.mkEq(Utils.hashCode(node.getBody).toString, "1")
        val typRefinements = typCxt.cxt.map(t => t.anno).toArray
        val totalSize = SmtUtils.mkAdd(sizes.toList: _*)
        val isBounded = SmtUtils.mkLe(totalSize, SIZE_BOUND.toString)
        val constraints = {
          val array: Array[String] = cfRelation ++ typRefinements :+ methodBodyCounter
          SmtUtils.mkAnd(array: _*)
        }
        val query = SmtUtils.mkForallImply(constraints, isBounded)
        val check = typecheck(query, node, "Method has unbounded size!")
        // solver.optimize(objective.asInstanceOf[ArithExpr])
        if (!check) {
          if (sizes.nonEmpty) {
            val methodStr = "Method: " + TreeUtils.enclosingClass(atypeFactory.getPath(node)).getSimpleName + "." + node.getName.toString
            val sizesStr = "Sizes: " + sizes.toString()
            val typCxtStr = "TypCxt: " + typCxt.toString()
            val queryStr = "Query: " + query
            Utils.logging(methodStr + "\n" + sizesStr + "\n" + typCxtStr + "\n" + queryStr)
          }
          // Utils.logging(SmtUtils.mkQueries(List("Assertions:\n", solver.getAssertions, SmtUtils.CHECK_SAT, SmtUtils.GET_OBJECTIVES, SmtUtils.GET_MODEL)))
        }
        check
      } else true
    }
    super.visitMethod(node, p)
    if (!isBounded) {
      val failCausesStr = {
        val currentCauses = failCauses.filter(f => f.enclosingMethod == node)
        if (currentCauses.nonEmpty) currentCauses.foldLeft("Fail causes:\n") { (acc, c) => acc + c + "\n" }
        else ""
      }
      Utils.logging(failCausesStr + "\n")
    } else {
      verifiedMethods += node
    }
    // localCollections ++= localTypCxt.filter { case (name, typ) => Utils.isCollectionTyp(typ.getTypElement(types)) }.values
    null
  }

  override def processClassTree(tree: ClassTree): Unit = {
    Utils.logging("Statistics: " + verifiedMethods.size + ", " + methodTrees.size + ", " + Z3Solver.TOTAL_QUERY + ", " + Z3Solver.TOTAL_TIME)
    super.processClassTree(tree)
  }

  private def typecheck(query: String, node: Tree, errorMsg: String): Boolean = {
    val ctx = Z3Solver.createContext
    val isChecked = Z3Solver.check(Z3Solver.parseSMTLIB2String(query, ctx), ctx)
    if (!isChecked) {
      // if (DEBUT_CHECK) println("\n-------\n" + query + "\n-------\n")
      if (DEBUG)
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
    val sameNameVars = typCxt.getVar(lhs.toString)
    if (sameNameVars.size == 1) {
      val lhsTyp = sameNameVars.head
      if (avoidAssignSubtyCheck(lhsTyp.isInput, node.getExpression)) return null
      val lhsTypMirror = lhsTyp.getErasedTypMirror(types)
      val lhsTypElement = lhsTyp.getTypElement(types)
      rhs match {
        case rhs: MethodInvocationTree =>
          val callSite = CallSite(rhs)
          val (method, _, receiverName, methodType) =
            (callSite.method, callSite.receiver, callSite.receiverName, callSite.methodType)
          if (methodType != null) {
            val isNext = Utils.isColWhat("next", types.erasure(methodType.getUnderlyingType), method.getElement, atypeFactory)
            val isIter = Utils.isColWhat("iterator", types.erasure(methodType.getUnderlyingType), method.getElement, atypeFactory)
            typCxt.cxt.foreach {
              t =>
                if (!t.isInput) {
                  if (isNext) { // x = z.next
                    val newAnno = SmtUtils.substitute(t.anno, List(label, receiverName),
                      List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkAdd(receiverName, "1")))
                    val implication = SmtUtils.mkForallImply(t.anno, newAnno)
                    typecheck(implication, node, "x = z.next")
                  } else if (isIter) { // z = x.iter
                    val newAnno = SmtUtils.substitute(t.anno, List(label, receiverName),
                      List(SmtUtils.mkAdd(label, "1"), "0"))
                    val implication = SmtUtils.mkForallImply(t.anno, newAnno)
                    typecheck(implication, node, "z = x.iter")
                  } else { // May be arbitrary update
                    val (reachableListFlds, recTyps) = Utils.getReachableFieldsAndRecTyps(lhsTypElement, elements, types, trees, HashSet[AccessPath](AccessPath(AccessPathHead(lhs.toString, lhsTypElement), List())))
                    if (reachableListFlds.nonEmpty) {
                      failCauses = failCauses + FailCause(node, "x = m(): May be arbitrary update!", TreeUtils.enclosingMethod(atypeFactory.getPath(node)))
                    }
                  }
                }
            }
          }
        case rhs@(_: MemberSelectTree | _: IdentifierTree) =>
          if (TypesUtils.isPrimitive(lhsTypMirror)) { // Primitive types
            typCxt.cxt.foreach { // Must not create alias
              t =>
                if (!t.isInput) {
                  val q = SmtUtils.substitute(t.anno,
                    List(label, lhs.toString),
                    List(SmtUtils.mkAdd(label, "1"), rhs.toString)
                  )
                  val implication = SmtUtils.mkForallImply(t.anno, q)
                  typecheck(implication, node, "x = y, x = y.f")
                }
            }
          } else { // Class types
            // May create alias for variables (1) whose types are application class (2) who have at least one access path to a list field
            val (reachableListFlds, recTyps) = Utils.getReachableFieldsAndRecTyps(lhsTypElement, elements, types, trees, HashSet[AccessPath](AccessPath(AccessPathHead(lhs.toString, lhsTypElement), List())))
            if (reachableListFlds.nonEmpty) {
              failCauses = failCauses + FailCause(node, "x = y, x = y.f: May create alias!", TreeUtils.enclosingMethod(atypeFactory.getPath(node)))
            }
          }
        case rhs: BinaryTree => // Must not create alias
          typCxt.cxt.foreach {
            t =>
              if (!t.isInput) {
                val left = rhs.getLeftOperand.toString
                val right = rhs.getRightOperand.toString
                val prefix = {
                  rhs.getKind match {
                    case Tree.Kind.PLUS => SmtUtils.mkAdd(left, right)
                    case Tree.Kind.MINUS => SmtUtils.mkSub(left, right)
                    case _ => rhs.toString // Let it fail
                  }
                }
                val q = SmtUtils.substitute(t.anno,
                  List(label, lhs.toString),
                  List(SmtUtils.mkAdd(label, "1"), prefix)
                )
                val implication = SmtUtils.mkForallImply(t.anno, q)
                typecheck(implication, node, "x = e_1 + e_2")
              }
          }
        case rhs: LiteralTree => // Must not create alias
          typCxt.cxt.foreach {
            t =>
              if (!t.isInput) {
                val q = SmtUtils.substitute(t.anno,
                  List(label, lhs.toString),
                  List(SmtUtils.mkAdd(label, "1"), rhs.toString)
                )
                val implication = SmtUtils.mkForallImply(t.anno, q)
                typecheck(implication, node, "x = n")
              }
          }
        case rhs: NewClassTree =>
          if (TypesUtils.isPrimitive(lhsTypMirror)) { // Primitive types
            typCxt.cxt.foreach { // Must not create alias
              t =>
                if (!t.isInput) {
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
              typCxt.cxt.foreach {
                t =>
                  if (!t.isInput) {
                    val q = SmtUtils.substitute(t.anno,
                      List(label, lhs.toString),
                      List(SmtUtils.mkAdd(label, "1"), "0")
                    )
                    val implication = SmtUtils.mkForallImply(t.anno, q)
                    typecheck(implication, node, "x = new List")
                  }
              }
            } else {
              val (reachableListFlds, recTyps) = Utils.getReachableFieldsAndRecTyps(lhsTypElement, elements, types, trees, HashSet[AccessPath](AccessPath(AccessPathHead(lhs.toString, lhsTypElement), List())))
              if (reachableListFlds.nonEmpty) {
                failCauses = failCauses + FailCause(node, "x = new Class(): May be arbitrary update!", TreeUtils.enclosingMethod(atypeFactory.getPath(node)))
              }
            }
          }
        case _ => // Do nothing
      }
    } else if (sameNameVars.size > 1) {
      issueWarning(node, Utils.nameCollisionMsg(lhs.toString))
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
    val (method, _, receiverName, methodType) =
      (callSite.method, callSite.receiver, callSite.receiverName, callSite.methodType)

    if (methodType != null) {
      val calleeSummary = getMethodSummaries(getMethodTypFromInvocation(node).getElement)
      val isAdd = Utils.isColWhat("add", types.erasure(methodType.getUnderlyingType), method.getElement, atypeFactory)
      val isRmv = Utils.isColWhat("remove", types.erasure(methodType.getUnderlyingType), method.getElement, atypeFactory)
      if (isAdd) Utils.logging("[list.add] line " + getLineNumber(node) + " " + node + "\n(" + getFileName + ")\n")
      typCxt.cxt.foreach { // Do not check iterator's and self's type annotation
        t =>
          if (!t.isInput) {
            val (_old: List[String], _new: List[String]) = {
              if (isAdd) { // y.add(x)
                (List(label, receiverName), List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkAdd(receiverName, "1")))
              } else if (isRmv) { // y.rmv()
                (List(label, receiverName), List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkSub(receiverName, "1")))
              } else { // x.m(); Assume method body has already been inlined
                val (_o, _n) = getArgUpdates(calleeSummary, receiverName)
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
      // val MAX_VAL = Integer.MAX_VALUE
      val MAY_CREATE_ALIAS = "alias"
      val UNKNOWN_UPDATE = "unknown"
      val (arg, argUpdate) = calleeSummary.foldLeft(List[String](), List[String]()) {
        (acc, summary) =>
          val increment: Integer = summary match {
            case MSumI(_, i) => i
            case MSumV(name, i) =>
              name match {
                case MAY_CREATE_ALIAS => failCauses = failCauses + FailCause(node, "x.m(): May create alias!", TreeUtils.enclosingMethod(atypeFactory.getPath(node))); 0
                case UNKNOWN_UPDATE => failCauses = failCauses + FailCause(node, "x.m(): May be arbitrary update!", TreeUtils.enclosingMethod(atypeFactory.getPath(node))); 0
                case _ => 0
              }
          }
          val (idx, accessPath) = MethodSumUtils.whichVar(summary, method.getElement)
          val target = {
            if (idx == -1) callerName
            else {
              node.getArguments.get(idx) match { // Assume all actual arguments are variables (i.e. have names)
                case arg: IdentifierTree => arg
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

  override def visitNewClass(node: NewClassTree, p: Void): Void = {
    // Consider new class also as a method invocation => Consider side effects (i.e. alias)
    // Assume: class initializers are inlined; Must not create alias
    // TreeUtils.constructor(node) // TODO: Inline class initializers
    super.visitNewClass(node, p)
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
      case t: NewClassTree => // x = new C; Must not create alias because we inline class initializers
        val rhsAnno = atypeFactory.getTypeAnnotation(t)
        // If rhs's annotation is empty or TOP
        if (rhsAnno == null || AnnotationUtils.areSameIgnoringValues(rhsAnno, atypeFactory.INVTOP))
          return true
      case m: MethodInvocationTree => // x = m(); Must not create alias
        val callee = getMethodTypFromInvocation(m).getElement
        // val receiver = TreeUtils.getReceiverTree(m)
        val receiverTyp = getTypeFactory.getReceiverType(m)
        if (receiverTyp == null) return false
        val isIter = Utils.isColWhat("iterator", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
        val isClone = rhsStr == "clone"
        val isRhsEmp = rhsStr.startsWith(EMP_COLLECTION_PREFIX) // || rhsStr.startsWith("Collections.unmodifiable")
        if (isIter || isClone || isRhsEmp) return true
      case _ =>
        if (rhsStr == "null") return true
    }
    false
  }

  private def initInv(inv: String, typCxt: TypCxt, node: Tree): String = {
    val vars = SmtUtils.extractSyms(inv).filter {
      v =>
        val sameNameVars = typCxt.getVar(v)
        if (sameNameVars.isEmpty) true
        else if (sameNameVars.size == 1) !sameNameVars.head.isInput
        else {
          issueWarning(node, Utils.nameCollisionMsg(v))
          sameNameVars.forall(t => !t.isInput)
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
  private def prepare(node: Tree): (TypCxt, TypCxt, String) = {
    val enclosingClass = TreeUtils.enclosingClass(atypeFactory.getPath(node))
    val enclosingMethod = TreeUtils.enclosingMethod(atypeFactory.getPath(node))
    val updatedLabel = getLabel(node)
    // if (enclosingClass == null || enclosingMethod == null)
    // Utils.logging("Empty enclosing class or method:\n" + node.toString)
    val fldInv = {
      if (enclosingClass == null) TypCxt(new HashSet[VarTyp])
      else atypeFactory.getFieldTypCxt(enclosingClass)
    }
    val localInv = {
      if (enclosingMethod == null) TypCxt(new HashSet[VarTyp])
      else atypeFactory.getLocalTypCxt(enclosingMethod, true)
    }
    (fldInv, localInv, updatedLabel)
  }

  private def getMethodTypFromInvocation(node: MethodInvocationTree): AnnotatedTypeMirror.AnnotatedExecutableType = atypeFactory.methodFromUse(node).methodType

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
            try {
              val res = Integer.parseInt(summary(1))
              acc + MSumI(summary.head, res)
            } catch {
              case e: Throwable => acc + MSumV(summary.head, summary(1))
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
    val method: AnnotatedTypeMirror.AnnotatedExecutableType = getMethodTypFromInvocation(node)
    val methodType: AnnotatedTypeMirror.AnnotatedDeclaredType = method.getReceiverType // method.getReceiverType // getTypeFactory.getReceiverType(node)
    val receiver: ExpressionTree = TreeUtils.getReceiverTree(node)
    val receiverName: String = if (receiver == null) "" else receiver.toString
    // val vtPairs: List[(VariableElement, AnnotatedTypeMirror)] = callee.getParameters.asScala.zip(atypeFactory.fromElement(callee).getParameterTypes.asScala).toList
  }

  private def getMethodElementFromDecl(node: MethodTree): ExecutableElement = {
    if (node == null)
      return null
    TreeUtils.elementFromDeclaration(node)
  }

  /**
    *
    * @param node a statement or expression
    * @return if it is in class constructor
    */
  private def isInConstructor(node: Tree): Boolean = {
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