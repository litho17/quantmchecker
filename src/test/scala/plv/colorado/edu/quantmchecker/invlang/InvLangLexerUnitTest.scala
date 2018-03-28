package plv.colorado.edu.quantmchecker

import org.scalatest.{FlatSpec, Matchers}
import plv.colorado.edu.quantmchecker.invlang.InvLangLexer

/**
  * @author Tianhan Lu
  */
class InvLangLexerUnitTest extends FlatSpec with Matchers {
  "Lex parse" should "success" in {
    InvLangUnitTestCases.lexerTests.foreach {
      test =>
        print(test + ": ")
        val lexres = InvLangLexer(test)
        if (lexres.isLeft) assert(false)
        else println(lexres.right)
    }
  }
}
