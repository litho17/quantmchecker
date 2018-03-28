package plv.colorado.edu.quantmchecker

import org.scalatest.{FlatSpec, Matchers}
import plv.colorado.edu.quantmchecker.invlang.InvLangCompiler

/**
  * @author Tianhan Lu
  */
class InvLangCompilerUnitTest extends FlatSpec with Matchers {
  InvLangUnitTestCases.parserTests.foreach {
    test =>
      print(test + ": ")
      val compres = InvLangCompiler(test)
      if (compres.isLeft) assert(false)
      else println(compres.right)
  }
}
