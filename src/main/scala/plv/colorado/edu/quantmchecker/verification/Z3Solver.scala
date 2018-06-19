package plv.colorado.edu.quantmchecker.verification

import java.util

import com.microsoft.z3.{BoolExpr, Context, Solver, Status}

/**
  * @author Tianhan Lu
  */
object Z3Solver {
  val DEBUG = false

  val cfg = new util.HashMap[String, String]
  cfg.put("model", "true")
  val ctx = new Context(cfg)

  val solver: Solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }

  def check(f: BoolExpr): Boolean = {
    if (DEBUG) println(f)
    val s = ctx.mkSolver
    s.add(f)
    interpretSolverOutput(s.check())
  }

  def parseSMTLIB2StringToArray(str: String): Array[BoolExpr] = {
    try {
      ctx.parseSMTLIB2String(str, null, null, null, null)
    } catch {
      case e: Exception => println("SMTLIB2 parse exception:\n" + str); Array(ctx.mkFalse())
    }
  }
  def parseSMTLIB2String(str: String): BoolExpr = ctx.mkAnd(parseSMTLIB2StringToArray(str): _*)

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new Exception("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  def optimizeExample(): Unit = {
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
