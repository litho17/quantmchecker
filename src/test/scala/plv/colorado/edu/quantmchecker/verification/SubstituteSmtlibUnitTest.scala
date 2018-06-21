package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class SubstituteSmtlibUnitTest extends FlatSpec with Matchers {
  "substitution" should "work" in {
    val _old = List("e", "ee")
    val _new = List("(+ c d)", "(* m n)")
    TestCases.coefficients.foreach {
      str =>
        val newStr = SmtUtils.substitute(str, _old, _new)
        println(str)
        println(newStr)
        println(SmtUtils.parseSmtlibToToken(newStr))
    }
  }

  "substitution" should "also work" in {
    val label = "c52"
    val receiverName = "it"
    val p = "= (+ self it) (- c54 c52)"
    val q = SmtUtils.substitute(p, List(label, receiverName),
      List(SmtUtils.mkAdd(label, "1"), SmtUtils.mkSub(receiverName,"1")))
    println(q)
  }
}
