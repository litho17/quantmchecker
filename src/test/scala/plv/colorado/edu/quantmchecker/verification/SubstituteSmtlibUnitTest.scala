package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}
import smtlib.lexer.Tokens.{CParen, OParen, SymbolLit}

/**
  * @author Tianhan Lu
  */
class SubstituteSmtlibUnitTest extends FlatSpec with Matchers {
  "substitution" should "work" in {
    val _old = List("e", "ee")
    val _new = List("(+ c d)", "(* m n)")
    TestCases.coefficients.foreach {
      str =>
        val tokens = VerifyUtils.parseSmtlibToToken(str)
        val newTokens = tokens.map {
          case t: SymbolLit =>
            val idx = _old.indexOf(t.content)
            if (idx != -1)
              SymbolLit(_new(idx))
            else
              t
          case x@_ => x
        }
        // tokens.foreach(t => println(t, t.getClass))
        // newTokens.foreach(t => println(t, t.getClass))
        val newStr = newTokens.foldLeft(""){
          (acc, t) =>
            if (t.kind == OParen)
              acc + "( "
            else if (t.kind == CParen)
              acc + ") "
            else
              acc + t.toString() + " "
        }
        println(str)
        println(newStr)
        println(VerifyUtils.parseSmtlibToToken(newStr))
    }
  }
}
