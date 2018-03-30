package plv.colorado.edu.quantmchecker.invlang

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class InvLangSolverUnitTest extends FlatSpec with Matchers {
  val tests = List(
    ("entrySet+<self>=+26-24", 0, 1, 24, false),
    ("INPUTINPUT+<self>.results=+22+24+26+28+30-16", 0, 1, 55, false),
    ("+<self>=+41", -1, 1, 41, true)
  )

  "Solver" should "success" in {
    tests.foreach {
      case (invariant, rem, self, line, res) =>
        val compilerResults = InvLangCompiler(invariant)
        if (compilerResults.isLeft) assert(false)
        else {
          // println(System.getProperty("java.library.path"))
          println(invariant)
          assert(res == InvWithSolver.isValidAfterUpdate(compilerResults.right.get, rem, self, line))
        }
    }
  }
}
