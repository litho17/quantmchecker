package plv.colorado.edu.quantmchecker.verification

import java.util

import com.microsoft.z3._
import plv.colorado.edu.quantmchecker.utils.PrintStuff

/**
  * @author Tianhan Lu
  */
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

  def optimize(f: BoolExpr, syms: Iterable[String], ctx: Context): Unit = {
    val opt = ctx.mkOptimize()
    opt.Add(f)
    println(f)
    f.
    val obj = ctx.mkAdd(syms.map(sym => ctx.mkIntConst(sym).asInstanceOf[ArithExpr]).toArray:_*)
    // println(opt.MkMaximize(obj))
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
