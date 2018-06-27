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
import plv.colorado.edu.quantmchecker.summarylang.{MSum, MSumI, MSumV, MethodSumUtils}
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import plv.colorado.edu.quantmchecker.verification.{CFRelation, SmtUtils, Z3Solver}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUG_PATHS = false
  private val DEBUG_WHICH_UNHANDLED_CASE = false
  // private val ISSUE_ALL_UNANNOTATED_LISTS = true

  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INC: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inc])
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

  private var iters: HashMap[String, Map[String, String]] = HashMap.empty // Names of annotated iterators in current method

  override def visitMethod(node: MethodTree, p: Void): Void = {
    iters = getVarsOfType(node, Utils.ITER_NEXT.map { case (c, m) => c })
    val typCxt = atypeFactory.getLocalTypCxt(node)
    typCxt.foreach { // Check each invariant is a valid SMTLIB2 string
      case (v, t) =>
        try {
          SmtUtils.parseSmtlibToToken(t)
        } catch {
          case e: Exception => assert(false)
        }
    }
    val inputVars = getInputVars(typCxt)
    typCxt.foreach { // Rule T-Init: No need to check iterator's or input's type annotation
      case (v, t) if !iters.contains(v) && !inputVars.contains(v) =>
        val init = initInv(t, typCxt)
        typecheck(SmtUtils.mkAssertionForall(init), node, "T-Init\n")
      case _ => true
    }
    if (node.getBody != null) { // Optimize for upper bound
      val listVars = getVarsOfType(node, Utils.COLLECTION_ADD.map { case (c, m) => c }).keySet
      if (listVars.nonEmpty) { // Only consider list variables
        val constraints = typCxt.foldLeft(new HashSet[String]) { // Collect constraints from types
          case (acc, (v, t)) =>
            acc + SmtUtils.mkAssertion({
              if (iters.contains(v)) {
                val attachedList = SmtUtils.threeTokensToOne({
                  iters.get(v) match {
                    case Some(map) => assert(map.size == 1); map.head._2
                    case None => ???
                  }
                })
                SmtUtils.mkAnd(">= " + v + " " + " 0", "<= " + v + " " + attachedList)
              } else {
                SmtUtils.substitute(t, List(SmtUtils.SELF, Utils.toInit(SmtUtils.SELF)), List(v, v))
              }
            })
        }
        val rcfa = (CFRelation.treeToCons(node.getBody) + SmtUtils.mkEq(Utils.hashCode(node.getBody), "1")).map(s => SmtUtils.mkAssertion(s))
        val syms = (rcfa ++ constraints).foldLeft(iters.keySet) { (acc, cons) => acc ++ SmtUtils.extractSyms(cons) }
        val decl = syms.foldLeft(new HashSet[String]) { (acc, sym) => acc + SmtUtils.mkDeclConst(sym) }
        val assertInit = syms.foldLeft(new HashSet[String]) {
          (acc, sym) => if (Utils.isInit(sym) && !inputVars.contains(sym)) acc + SmtUtils.mkAssertion(SmtUtils.mkEq(sym, "0")) else acc
        }
        val objective = {
          if (listVars.size == 1) listVars.head
          else SmtUtils.mkAdd(listVars.toArray: _*)
        }
        val preps = SmtUtils.mkQueries(decl.toList ::: assertInit.toList ::: constraints.toList ::: rcfa.toList)
        val query = SmtUtils.mkQueries(List(preps, SmtUtils.mkMaximize(objective), SmtUtils.CHECK_SAT))
        if (constraints.nonEmpty) println(query)
        // val ctx = Z3Solver.createContext
        // Z3Solver.optimize(Z3Solver.parseSMTLIB2String(preps, ctx), listVars.keySet, ctx)
        typecheck(query, node, "Method has unbounded size!")
      }
    }
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
      }
    }
    Utils.logging("Field lists: " + atypeFactory.fieldLists.size + "\nLocal lists: " + atypeFactory.localLists.size)
    super.processClassTree(classTree)
  }

  /**
    *
    * @param query    a query
    * @param node     AST node
    * @param errorMsg error message if query is not satisfiable
    */
  private def typecheck(query: String, node: Tree, errorMsg: String): Boolean = {
    val ctx = Z3Solver.createContext
    val isChecked = Z3Solver.check(Z3Solver.parseSMTLIB2String(query, ctx), ctx)
    if (!isChecked) {
      // if (DEBUT_CHECK) println("\n-------\n" + query + "\n-------\n")
      issueError(node, errorMsg)
    }
    isChecked
  }

  /**
    *
    * @param list   a list variable
    * @param typMap typing context
    * @return all iterators in the typing context that are attached to v
    */
  private def getListIters(list: String, typMap: Map[String, String]): HashSet[String] = {
    typMap.foldLeft(new HashSet[String]) {
      case (acc, (v, t)) => if (SmtUtils.threeTokensToOne(t) == list) acc + v else acc
    }
  }

  /**
    *
    * @param node method
    * @return all local variables (and their types) in the method that belong to one of the target types
    */
  private def getVarsOfType(node: MethodTree, targetType: HashSet[String]): HashMap[String, Map[String, String]] = {
    if (node.getBody != null) {
      Utils.flattenStmt(node.getBody).foldLeft(new HashMap[String, Map[String, String]]) {
        (acc, stmt) =>
          stmt match {
            case v: VariableTree =>
              val element = TreeUtils.elementFromTree(v)
              val typ = types.erasure(trees.getTypeMirror(trees.getPath(element)))
              val typeElement = types.asElement(typ)
              if (typeElement != null) {
                val isTargetClass = targetType.exists { c => c.contains(typeElement.toString) }
                if (isTargetClass) {
                  val map = atypeFactory.getVarAnnoMap(v)
                  if (map.isEmpty) acc
                  else acc + (v.getName.toString -> map)
                } else acc
              } else acc
            case _ => acc
          }
      }
    } else HashMap.empty
  }

  // Assume that all variables' scope is global to a method
  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    if (!isEnclosedInExprStmt(node))
      return super.visitAssignment(node, p)

    val (fieldInvs, localInvs, label) = prepare(node)
    val typingCxt = fieldInvs ++ localInvs
    val lhs = node.getVariable
    val rhs = node.getExpression
    // val lhsTyp = atypeFactory.getAnnotatedType(node.getVariable)
    // val lhsAnno = lhsTyp.getAnnotations
    val lhsTyp = inferVarType(node.getVariable.toString, typingCxt) // self -> ...self...
    val rhsTyp = { // self -> ...self...
      val set = inferExprType(node.getExpression, typingCxt)
      if (set.nonEmpty) set + SmtUtils.mkEq(Utils.hashCode(rhs), SmtUtils.SELF) else set
    }.map { s => SmtUtils.substitute(s, List(label, lhs.toString), List(SmtUtils.mkAdd(label, "1"), SmtUtils.SELF)) }

    rhs match {
      case rhs: MethodInvocationTree =>
        val callSite = CallSite(rhs)
        val (callee, caller, callerName, callerTyp) =
          (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp)
        if (callerTyp != null) {
          val isNext = Utils.isColWhat("next", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)
          val isRmv = Utils.isColWhat("remove", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)
          val iterators = getListIters(callerName, typingCxt).toList
          typingCxt.foreach { // Do not check iterator's and self's type annotation
            case (v, t) if !iters.contains(v) && v != callerName =>
              val tp = SmtUtils.substitute(t, List(SmtUtils.SELF), List(v))
              if (isNext) {
                {
                  val p = tp
                  val q = SmtUtils.substitute(p, List(label, callerName),
                    List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkSub(callerName, "1")))
                  val implication = SmtUtils.mkImply(p, q)
                  typecheck(implication, node, "y = x.next: invariant broken due to line counter increment")
                }
                {
                  val p = {
                    val listName = SmtUtils.threeTokensToOne(callerName)
                    // TODO: If x: List[t], get t's type annotation
                    SmtUtils.FALSE
                  }
                  val q = SmtUtils.conjunctionAll(lhsTyp)
                  val implication = SmtUtils.mkImply(p, q)
                  typecheck(implication, node,
                    "y = x.next: invariant broken due to incompatible types between x's element and y")
                }
              }
            case _ =>
          }
          // Check self's type annotation
          if (isRmv) {
            lhsTyp.foreach {
              t =>
                val p = t
                val _old = label :: SmtUtils.SELF :: iterators
                val _new = SmtUtils.mkAdd(label, "1") :: SmtUtils.mkSub(SmtUtils.SELF, "1") ::
                  iterators.map(s => SmtUtils.mkSub(s, "1"))
                val q = SmtUtils.substitute(p, _old, _new)
                val implication = SmtUtils.mkImply(p, q)
                typecheck(implication, node, "y = x.remove: invariant broken")
            }
          }
        } else {
          if (avoidAssignSubtyCheck(node.getExpression)) {
            null
          } else {
            super.visitAssignment(node, p)
          }
        }
      case _ =>
        val implication = SmtUtils.mkImply(SmtUtils.conjunctionAll(rhsTyp), SmtUtils.conjunctionAll(lhsTyp))
        typecheck(implication, node, "x = e: rhs's type doesn't imply lhs's")
        typingCxt.foreach {
          case (v, t) =>
            if (!atypeFactory.isDependentOn(lhs.toString, t)) { // No need to check because this is already checked above
              val q = SmtUtils.substitute(t, List(label), List(SmtUtils.mkAdd(label, "1")))
              val implication = SmtUtils.mkImply(t, q)
              typecheck(implication, node, "x = e: invariant invalidated due to counter increment")
            }
        }
    }
    /**
      * This is unsound because of breaking subtype checking, but it is implemented for reducing annotation burden
      */
    null
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
    val typingCxt = fieldInvs ++ localInvs
    // TODO: methodinvocation (a.f().g()) -> memberselect (a.f())
    val callSite = CallSite(node)
    val (callee, caller, callerName, callerTyp, callerDecl, vtPairs) =
      (callSite.callee, callSite.caller, callSite.callerName, callSite.callerTyp, callSite.callerDecl, callSite.vtPairs)

    if (callerTyp != null) {
      /*val argInc = vtPairs.foldLeft(List[HashMap[String, String]]()) {
        case (acc, (v, t: AnnotatedTypeMirror)) =>
          val anno = atypeFactory.getTypeAnnotation(t.getAnnotations)
          if (anno != null) atypeFactory.getVarAnnoMap(anno, INC) :: acc else HashMap[String, String]() :: acc
      }
      val calleeTree = trees.getTree(callee)
      val calleeTypCxt = if (calleeTree != null && calleeTree.getBody != null) atypeFactory.getLocalTypCxt(calleeTree) else HashMap.empty*/

      // val callerSummary = getMethodSummaries(getMethodElementFromDecl(getEnclosingMethod(node)))
      val calleeSummary = getMethodSummaries(getMethodElementFromInvocation(node))
      val isAdd = Utils.isColWhat("add", types.erasure(callerTyp.getUnderlyingType), callee, atypeFactory)
      if (isAdd) Utils.logging("[list.add] line " + getLineNumber(node) + " (" + getFileName + ")")
      val iterators = getListIters(callerName, typingCxt).toList
      typingCxt.foreach { // Do not check iterator's and self's type annotation
        case (v, t) if !iters.contains(v) && !v.startsWith(callerName) =>
          val tp = SmtUtils.substitute(t, List(SmtUtils.SELF), List(v), true)
          val p = tp
          val (_old: List[String], _new: List[String], extraCons: HashSet[String]) = {
            if (isAdd) {
              val o = label :: callerName :: iterators
              val n = SmtUtils.mkAdd(label, "1") :: SmtUtils.mkAdd(callerName, "1") ::
                iterators.map(s => SmtUtils.mkAdd(s, "1"))
              (o, n, HashSet.empty)
            } else {
              val (_o, _n) = getArgUpdates(calleeSummary, callerName)
              val o = label :: _o ::: iterators
              val n = SmtUtils.mkAdd(label, "1") :: _n ::: iterators.map(s => SmtUtils.mkAdd(s, "1"))
              (o, n, HashSet[String]())
            }
          }
          val q = SmtUtils.substitute(p, _old, _new)
          val implication = SmtUtils.mkImply(SmtUtils.conjunctionAll(p :: extraCons.toList), q)
          typecheck(implication, node, "y.add(x): invariant broken on dependent types")
        case _ =>
      }
      // Check self's type annotation
      if (!isAdd) {
        inferVarType(callerName, typingCxt).foreach {
          t =>
            val p = t
            val tokens = SmtUtils.parseSmtlibToToken(t)
            val selfs = tokens.filter(t => t.toString().startsWith(SmtUtils.SELF)).map(t => t.toString())
            val (_o, _n) = getArgUpdates(calleeSummary, "self")
            val _old = label :: _o ::: iterators
            val _new = SmtUtils.mkAdd(label, "1") :: _n ::: iterators.map(s => SmtUtils.mkAdd(s, "1"))
            val q = SmtUtils.substitute(p, _old, _new)
            val implication = SmtUtils.mkImply(p, q)
            typecheck(implication, node, "y.add(x): invariant broken on self type")
        }
      }
    }

    def getArgUpdates(calleeSummary: HashSet[MSum], callerName: String): (List[String], List[String]) = {
      val (arg, argUpdate) = calleeSummary.foldLeft(List[String](), List[String]()) {
        (acc, summary) =>
          val increment: Integer = summary match {
            case MSumI(_, i) => i
            case _ => 0
          }
          val (idx, accessPath) = MethodSumUtils.whichVar(summary, callee)
          val target = {
            if (idx == -1) callerName
            else {
              node.getArguments.get(idx) match {
                case arg: IdentifierTree => arg
                case _ => "" // E.g. o.m(y.n()+z)
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
    val (fieldInvs, localInvs, updatedLabel) = prepare(node)
    (fieldInvs ++ localInvs).foreach {
      /*Tree.Kind.POSTFIX_INCREMENT
                     | Tree.Kind.PREFIX_INCREMENT
                     | Tree.Kind.POSTFIX_DECREMENT
                     | Tree.Kind.PREFIX_DECREMENT
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
        val receiverTyp = getTypeFactory.getReceiverType(m)
        if (receiverTyp == null)
          return false
        val isIter = Utils.isColWhat("iterator", types.erasure(receiverTyp.getUnderlyingType), callee, atypeFactory)
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
    * @param inv    invariant
    * @param typCxt typing context
    * @return the (symbolic) initial value of the invariant
    */
  private def initInv(inv: String, typCxt: Map[String, String]): String = {
    val tokens = SmtUtils.parseSmtlibToToken(inv)
    val selfs = tokens.filter(t => t.toString().startsWith(SmtUtils.SELF)).map(t => t.toString()) // init(self) = 0
    val counters = tokens.filter(t => SmtUtils.isLineCounter(t.toString())).map(t => t.toString()) // init(counter) = 0
    val (iterators, lists) = { // init(it) = list_init
      typCxt.foldLeft(List[String](), List[String]()) {
        case (acc, (v, t)) => if (iters.contains(v)) {
          (v :: acc._1, SmtUtils.threeTokensToOne(t) + "_" + SmtUtils.INIT :: acc._2)
        } else acc
      }
    }
    val (vars, initVars) = { // init(x) = x_init; init(x_init) = x_init
      val vars = SmtUtils.extractSyms(inv).diff(iters.keySet).toList
      (vars, vars.map { v => if (Utils.isInit(v)) v else Utils.toInit(v) })
    }
    val _old: List[String] = selfs ::: counters ::: vars ::: iterators
    val _new: List[String] = selfs.map(_ => "0") ::: counters.map(_ => "0") ::: initVars ::: lists
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
    * @param v      name of a variable
    * @param typCxt a typing context
    * @return all types in the typing context that is dependent on
    *         the given variable name (e.g. v -> {...self...}/v.f -> {...self...})
    */
  private def inferVarType(v: String, typCxt: Map[String, String]): HashSet[String] = {
    val selfTyp: HashSet[String] = typCxt.get(v) match {
      case Some(s) => HashSet(s)
      case None => HashSet.empty
    }
    val dependentTyp = typCxt.foldLeft(new HashSet[String]) {
      case (acc2, (vInEnv, typInEnv)) =>
        if (SmtUtils.containsToken(typInEnv, v) && !iters.contains(vInEnv)) // Do not consider iterators as being dependent on
          acc2 + SmtUtils.substitute(typInEnv, List(SmtUtils.SELF), List(vInEnv), true) // E.g. self -> vInEnv
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

  private def getFileName: String = {
    val absPath = root.getSourceFile.getName
    if (absPath.startsWith(Utils.DESKTOP_PATH + File.separator)) absPath.substring(Utils.DESKTOP_PATH.length + 1) else absPath
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

  /**
    *
    * @param method a method
    * @return the summary of the method
    */
  private def getMethodSummaries(method: ExecutableElement): HashSet[MSum] = {
    if (method == null)
      return new HashSet[MSum]
    val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY)).toList
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

  def getInputVars(typCxt: HashMap[String, String]): Set[String] = {
    typCxt.filter {
      case (v, t) => Utils.isInit(v) // Because v_init is automatically generated in getVarAnnoMap for @Input
    }.keySet
  }

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
