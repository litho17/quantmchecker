package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class SmtlibStrToLpConstraint extends FlatSpec with Matchers {
  "lp constraint generation" should "be successful" in {
    TestCases.counters.foreach {
      str => println(SmtUtils.parseSmtlibStrToLpCons(str))
    }
  }
}
