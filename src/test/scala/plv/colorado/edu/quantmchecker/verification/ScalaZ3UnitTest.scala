package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FunSuite, Matchers}
import plv.colorado.edu.quantmchecker.invlang.InvSolver
import z3.scala.dsl.{Val, findAll}

/**
  * @author Tianhan Lu
  */
class ScalaZ3UnitTest extends FunSuite with Matchers {

  def isPrime(i: Int): Boolean = {
    !(2 to i - 1).exists(i % _ == 0)
  }

  test("ForComprehension") {
    // println(System.getProperty("java.class.path"))
    val results = for (
      (x, y) <- findAll[Int, Int]((x: Val[Int], y: Val[Int]) => x > 0 && y > x && x * 2 + y * 3 <= 40);
      if (isPrime(y));
      z <- findAll((z: Val[Int]) => z * x === 3 * y * y))
      yield (x, y, z)

    results.size should equal(8)
  }

  TestCases.queries.foreach(s => println(InvSolver.parseStringAndCheck(s)))


  // println(InvSolver.parseFileAndCheck(Utils.DESKTOP_PATH + "/z3_capability.txt"))
}