package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class Z3UnitTest extends FlatSpec with Matchers {

  val testCases = List("+ len(x) rem(y) init(z) self 7 c1 w", "")
  "Z3" should "work" in {
    Z3Solver.optimizeExample()
    strQueryExample()
  }

  def strQueryExample(): Unit = {
    TestCases.queries.foreach {
      str =>
        val ctx = Z3Solver.createContext
        Z3Solver.check(Z3Solver.parseSMTLIB2String(str, ctx), ctx)
    }
  }
}
