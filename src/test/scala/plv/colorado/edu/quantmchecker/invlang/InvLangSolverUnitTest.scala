package plv.colorado.edu.quantmchecker.invlang

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class InvLangSolverUnitTest extends FlatSpec with Matchers {
  val tests = List(
    ("+x.f=-y.g+c26-c24", ("y.g", 1), ("x.f", 0), "c24", false),
    ("+x.f=-y.g+c22+c24+c26+c28+c30-c16", ("y.g", 1), ("x.f", 0), "c55", false),
    ("+x.f=+c41", ("", 0), ("x.f", 1), "c41", true)
  )

  "Solver" should "success" in {
    tests.foreach {
      case (invariant, rem, self, line, res) =>
        val compilerResults = InvLangCompiler(invariant)
        if (compilerResults.isLeft) {
          assert(false)
        } else {
          // println(System.getProperty("java.library.path"))
          println(invariant)
          assert(res == InvWithSolver.isValidAfterUpdate(compilerResults.right.get, rem, self, line))
        }
    }
  }
}
