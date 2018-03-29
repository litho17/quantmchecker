package plv.colorado.edu.quantmchecker.solver

import org.scalatest.{FunSuite, Matchers}
import z3.scala.dsl.{Val, findAll}

/**
  * @author Tianhan Lu
  */
class SolverUnitTest extends FunSuite with Matchers {

  def isPrime(i: Int): Boolean = {
    !(2 to i - 1).exists(i % _ == 0)
  }

  test("ForComprehension") {
    println(System.getProperty("java.class.path"))
    val results = for (
      (x, y) <- findAll[Int, Int]((x: Val[Int], y: Val[Int]) => x > 0 && y > x && x * 2 + y * 3 <= 40);
      if (isPrime(y));
      z <- findAll((z: Val[Int]) => z * x === 3 * y * y))
      yield (x, y, z)

    results.size should equal(8)
  }
}