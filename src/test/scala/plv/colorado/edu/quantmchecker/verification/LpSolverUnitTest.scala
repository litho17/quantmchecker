package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp._
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
class LpSolverUnitTest extends FlatSpec with Matchers {
  private def debug(problem: Problem): Unit = {
    problem.getConstraints.asScala.foreach(c => println(c))
    println(problem.getObjective, problem.getOptType)
  }

  /**
    * Remember to Edit Configuration of this test:
    * Set DYLD_LIBRARY_PATH to the absolute path of the path that contains liblpsolve55.dylib, liblpsolve55.a
    * (e.g. /Users/lumber/Documents/workspace/quantmchecker/lib)
    * Reference:
    * 1. https://diegoresearch.wordpress.com/2008/07/10/using-lp_solve-in-java-with-mac-os-x/
    * 2. http://lpsolve.sourceforge.net/5.5/
    * 3. https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.5/
    */
  "lp solver" should "work" in {
    val factory = new SolverFactoryLpSolve()
    factory.setParameter(Solver.VERBOSE, 0)
    factory.setParameter(Solver.TIMEOUT, 100) // set timeout to 100 seconds
    val problem = new Problem()

    /**
      * Constructing a Problem:
      * Maximize: 143x+60y
      * Subject to:
      * 120x+210y <= 15000
      * 110x+30y <= 4000
      * x+y <= 75
      *
      * With x,y being integers
      *
      */

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

    System.out.println(result, assert(result.getObjective.intValue() == 6266))

    /**
      * Extend the problem with x <= 16 and solve it again
      */
    problem.setVarUpperBound("x", 16)

    solver = factory.get
    result = solver.solve(problem)

    System.out.println(result, assert(result.getObjective.intValue() == 5828))
  }

  "lp solver" should "work as well" in {
    val factory = new SolverFactoryLpSolve()
    factory.setParameter(Solver.VERBOSE, 0)
    factory.setParameter(Solver.TIMEOUT, 100)
    val problem = new Problem()
    val symbols = List("c1", "c2", "c3", "c4", "c5", "c6", "c7")
    symbols.foreach(sym => problem.setVarType(sym, classOf[Integer]))
    symbols.foreach(sym => problem.setVarLowerBound(sym, 0))
    /**
      *
      * (assert (= c3 (+ c1 c2)))
      * (assert (= c3 c6))
      * (assert (= c3 1))
      * (assert (= c6 1))
      * (assert (= c7 (* c6 1000)))
      * (assert (= c7 c4))
      * (assert (= c7 c5))
      * (assert (>= c1 0))
      * (assert (>= c2 0))
      * (assert (>= c3 0))
      * (assert (>= c4 0))
      * (assert (>= c5 0))
      * (assert (>= c6 0))
      * (assert (>= c7 0))
      * (maximize (- (+ c1 c4) c5))
      */
    val cons1 = new Linear
    cons1.add(1, symbols(0))
    cons1.add(1, symbols(1))
    cons1.add(-1, symbols(2))
    problem.add(cons1, "=", 0)

    val cons2 = new Linear
    cons2.add(-1, symbols(2))
    cons2.add(1, symbols(5))
    problem.add(cons2, "=", 0)

    val cons3 = new Linear
    cons3.add(1, symbols(2))
    problem.add(cons3, "=", 1)

    val cons4 = new Linear
    cons4.add(1, symbols(5))
    problem.add(cons4, "=", 1)

    val cons5 = new Linear
    cons5.add(1000, symbols(5))
    cons5.add(-1, symbols(6))
    problem.add(cons5, "=", 0)

    val cons6 = new Linear
    cons6.add(1, symbols(3))
    cons6.add(-1, symbols(6))
    problem.add(cons6, "=", 0)

    val cons7 = new Linear
    cons7.add(1, symbols(4))
    cons7.add(-1, symbols(6))
    problem.add(cons7, "=", 0)

    val obj = new Linear
    obj.add(1, symbols(0))
    // obj.add(1, symbols(1))
    obj.add(1, symbols(3))
    obj.add(-1, symbols(4))
    problem.setObjective(obj, OptType.MAX)

    debug(problem)

    val result = factory.get.solve(problem)
    println(result, assert(result.getObjective.intValue() == 1))
  }

  "lp solver" should "work?" in {
    val symbols = List("c1", "c2", "c3")

    val cons1 = new Linear
    cons1.add(1, symbols(0))
    cons1.add(1, symbols(1))
    cons1.add(-1, symbols(2))

    val cons3 = new Linear
    cons3.add(1, symbols(2))

    val obj = new Linear
    obj.add(1, symbols(0))

    val result = VerifyUtils.solveLp(
      List(LpCons(cons1, "=", 0), LpCons(cons3, "=", 1)),
      Some(obj),
      0,
      OptType.MAX
    )
    result match {
      case Some(res) => assert(res.getObjective.intValue() == 1)
      case None => assert(false)
    }
    println(result)
  }
}
