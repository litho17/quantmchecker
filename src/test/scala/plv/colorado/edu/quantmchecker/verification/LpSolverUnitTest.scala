package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp._
import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Tianhan Lu
  */
class LpSolverUnitTest extends FlatSpec with Matchers {
  /**
    * Remember to Edit Configuration of this test:
    * Set DYLD_LIBRARY_PATH to the absolute path of the path that contains liblpsolve55.dylib, liblpsolve55.a
    * Reference:
    * https://diegoresearch.wordpress.com/2008/07/10/using-lp_solve-in-java-with-mac-os-x/
    * http://lpsolve.sourceforge.net/5.5/
    * https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.5/
    */
  "lp solver" should "work" in {
    val factory = new SolverFactoryLpSolve()
    factory.setParameter(Solver.VERBOSE, 0)
    factory.setParameter(Solver.TIMEOUT, 100)
    val problem = new Problem()

    var linear = new Linear
    linear.add(143, "x")
    linear.add(60, "y")

    problem.setObjective(linear, OptType.MAX)

    linear = new Linear
    linear.add(120, "x")
    linear.add(210, "y")

    problem.add(linear, "<=", 15000)

    linear = new Linear
    linear.add(110, "x")
    linear.add(30, "y")

    problem.add(linear, "<=", 4000)

    linear = new Linear
    linear.add(1, "x")
    linear.add(1, "y")

    problem.add(linear, "<=", 75)

    problem.setVarType("x", classOf[Integer])
    problem.setVarType("y", classOf[Integer])

    var solver = factory.get
    // you should use this solver only once for one problem
    var result = solver.solve(problem)

    System.out.println(result)

    /**
      * Extend the problem with x <= 16 and solve it again
      */
    problem.setVarUpperBound("x", 16)

    solver = factory.get
    result = solver.solve(problem)

    System.out.println(result)
  }
}
