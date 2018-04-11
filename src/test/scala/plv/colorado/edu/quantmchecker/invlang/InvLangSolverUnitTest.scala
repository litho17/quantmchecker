package plv.colorado.edu.quantmchecker.invlang

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class InvLangSolverUnitTest extends FlatSpec with Matchers {
  val tests = List(
    ("entrySet+<self>=+c26-c24", 0, 1, "c24", false),
    ("INPUTINPUT+<self>.results=+c22+c24+c26+c28+c30-c16", 0, 1, "c55", false),
    ("+<self>=+c41", -1, 1, "c41", true)
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
