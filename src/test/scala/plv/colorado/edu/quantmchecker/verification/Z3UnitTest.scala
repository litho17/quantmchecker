package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class Z3UnitTest extends FlatSpec with Matchers {
  val testCases = List(
    "(+ (len x) (rem y) (init z) self 7 c1 w)",
    "",
    "(= self (+ a 5))",
    "br",
    """
      |(declare-fun x () Int)
      |(declare-fun y () Int)
      |(declare-fun z () Int)
      |(assert (>= (* 2 x) (+ y z)))
      |(declare-fun f (Int) Int)
      |(declare-fun g (Int Int) Int)
      |(assert (< (f x) (g x x)))
      |(assert (> (f y) (g x x)))
      |(check-sat)
      |(get-model)
      |(push)
      |(assert (= x y))
      |(check-sat)
    """.stripMargin)
  "Z3" should "work" in {
    // Z3Solver.optimizeExample()

    // strQueryExample()


    val solver = new Z3Solver
    val a1 = solver.mkIntVar("a")
    val a2 = solver.mkIntVar("a")
    val self = solver.mkIntVar("self")
    assert(a1 == a2)
    solver.ctx.mkConstDecl("self", solver.ctx.getIntSort)
    val res = Z3Solver.parseStrToZ3AST(testCases(3), solver)
    // println(parse.getASTKind)
    res.getArgs.foreach {
      astNode =>
        println(astNode.toString, astNode == solver.getVar("br"))
        val args = astNode.getArgs
    }
    // println(parse.getSExpr)
  }

  def strQueryExample(): Unit = {
    TestCases.queries.foreach {
      str =>
        val ctx = Z3Solver.createContext
        Z3Solver.check(Z3Solver.parseSMTLIB2String(str, ctx), ctx)
    }
  }
}
