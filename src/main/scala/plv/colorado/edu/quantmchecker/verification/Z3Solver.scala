package plv.colorado.edu.quantmchecker.verification

import java.util

import com.microsoft.z3._
import plv.colorado.edu.quantmchecker.utils.PrintStuff

import scala.collection.immutable.HashMap

/**
  * @author Tianhan Lu
  */
class Z3Solver {
  val ctx: Context = new Context
  val solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }

  var names: HashMap[String, AST] = new HashMap[String, AST]

  def checkSAT: Boolean = interpretSolverOutput(solver.check)

  def checkSATWithAssumptions(assumes: List[String]): Boolean =
    interpretSolverOutput(solver.check(assumes.map(assume => ctx.mkBoolConst(assume)): _*))

  def push(): Unit = solver.push()

  def pop(): Unit = solver.pop()

  def getUNSATCore: String = sys.error("Unimp")

  private def interpretSolverOutput(status: Status): Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new Exception("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  def getVar(k: String): AST ={
    names.get(k) match {
      case Some(v) => v
      case None =>
        val ast = mkIntVar(k)
        names += (k -> ast)
        ast
    }
  }

  def mkAssert(a: AST): Unit = solver.add(a.asInstanceOf[BoolExpr])

  def mkNot(o: AST): AST = ctx.mkNot(o.asInstanceOf[BoolExpr])

  def mkEq(lhs: AST, rhs: AST): AST = ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])

  def mkNe(lhs: AST, rhs: AST): AST = ctx.mkNot(ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]))

  def mkGt(lhs: AST, rhs: AST): AST = ctx.mkGt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkLt(lhs: AST, rhs: AST): AST = ctx.mkLt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkGe(lhs: AST, rhs: AST): AST = ctx.mkGe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkLe(lhs: AST, rhs: AST): AST = ctx.mkLe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkAdd(lhs: AST, rhs: AST): AST = ctx.mkAdd(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkAdd(ast: AST*): AST = ctx.mkAdd(ast.map(a => a.asInstanceOf[ArithExpr]):_*)

  def mkSub(lhs: AST, rhs: AST): AST = ctx.mkSub(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkMul(lhs: AST, rhs: AST): AST = ctx.mkMul(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkDiv(lhs: AST, rhs: AST): AST = ctx.mkDiv(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkRem(lhs: AST, rhs: AST): AST = ctx.mkMod(lhs.asInstanceOf[IntExpr], rhs.asInstanceOf[IntExpr])

  def mkImplies(lhs: AST, rhs: AST): AST = ctx.mkImplies(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkAnd(lhs: AST, rhs: AST): AST = ctx.mkAnd(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkOr(lhs: AST, rhs: AST): AST = ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkXor(lhs: AST, rhs: AST): AST = ctx.mkXor(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkIntVal(i: Int): AST = ctx.mkInt(i)

  def mkBoolVal(b: Boolean): AST = ctx.mkBool(b)

  def mkIntVar(s: String): AST = ctx.mkIntConst(s)

  def mkBoolVar(s: String): AST = ctx.mkBoolConst(s)
}

object Z3Solver {
  val DEBUG = true

  val cfg = new util.HashMap[String, String]
  cfg.put("model", "true")

  def createSolver(ctx: Context): Solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }

  def createContext: Context = new Context(cfg)

  def optimize(obj: Expr, ctx: Context): Unit = {
    val opt = ctx.mkOptimize()
    println(opt.MkMaximize(obj))
  }

  def check(f: BoolExpr, ctx: Context): Boolean = {
    val s = createSolver(ctx)
    s.add(f)
    interpretSolverOutput(s.check(), f)
  }

  def parseSMTLIB2StringToArray(str: String, ctx: Context): Array[BoolExpr] = {
    try {
      ctx.parseSMTLIB2String(str, null, null, null, null)
    } catch {
      case e: Exception => PrintStuff.printCyanString("SMTLIB2 parse exception:\n" + str + "\n"); Array(ctx.mkFalse())
    }
  }

  def parseSMTLIB2String(str: String, ctx: Context): BoolExpr = {
    val array = parseSMTLIB2StringToArray(str, ctx)
    if (array.length == 1) array.head
    else if (array.isEmpty) ctx.mkTrue()
    else ctx.mkAnd(parseSMTLIB2StringToArray(str, ctx): _*)
  }

  private def interpretSolverOutput(status: Status, f: BoolExpr): Boolean = status match {
    case Status.UNSATISFIABLE => if (DEBUG) PrintStuff.printRedString("Unsat query:\n" + f); false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new Exception("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  @deprecated
  def optimizeExample(): Unit = {
    val ctx = new Context(cfg)
    println("Opt")
    val opt = ctx.mkOptimize
    // Set constraints.
    val xExp = ctx.mkIntConst("x")
    val yExp = ctx.mkIntConst("y")
    opt.Add(
      ctx.mkEq(ctx.mkAdd(xExp, yExp), ctx.mkInt(10)), // x + y = 10
      ctx.mkGe(xExp, ctx.mkInt(0)), // x >= 0
      ctx.mkGe(yExp, ctx.mkInt(0)) // y >= 0
    )
    // Set objectives.
    val mx = opt.MkMaximize(xExp)
    val my = opt.MkMaximize(yExp)
    println(opt.Check)
    println(mx)
    println(my)
  }
}
