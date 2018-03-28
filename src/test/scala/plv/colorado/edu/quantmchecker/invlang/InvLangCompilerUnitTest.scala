package plv.colorado.edu.quantmchecker.invlang

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class InvLangCompilerUnitTest extends FlatSpec with Matchers {
  InvLangUnitTestCases.parserTests.foreach {
    test =>
      print(test + ": ")
      val compilerResults = InvLangCompiler(test)
      if (compilerResults.isLeft) assert(false)
      else println(compilerResults.right)
  }
}
