package plv.colorado.edu.quantmchecker.solver

import org.scalatest.{FunSuite, Matchers}
import plv.colorado.edu.quantmchecker.invlang.InvSolver
import z3.scala.dsl.{Val, findAll}

/**
  * @author Tianhan Lu
  */
class SolverUnitTest extends FunSuite with Matchers {

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

  private val queries = List[String](
    """
      (assert
              (forall
                ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
                (implies
                  (= (+ a (* d (+ b (* b f)))) (* (- c e) (+ b (* b f))))
                  (= (+ (+ a (+ b (* b f))) (* d (+ b (* b f)))) (* (- (+ c 1) e) (+ b (* b f))))
                )
              )
            )
    """.stripMargin,
    """
      (assert
              (forall
                ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
                (implies
                  (= (+ a (* d (+ b (* b f)))) (* (- c e) (+ b (* b f))))
                  (= (+ a (* (- d 1) (+ b (* b f)))) (* (- c (+ e 1)) (+ b (* b f))))
                )
              )
            )
    """.stripMargin
  )

  queries.foreach(s => println(InvSolver.parseStringAndCheck(s)))


  // println(InvSolver.parseFileAndCheck(Utils.DESKTOP_PATH + "/z3_capability.txt"))
}