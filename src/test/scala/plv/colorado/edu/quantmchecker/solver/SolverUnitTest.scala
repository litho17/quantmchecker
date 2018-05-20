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
                ((a Int) (b Int) (c Int) (d Int) (e Int) (f.g Int))
                (implies
                  (= (+ a (* d (+ b (* b f.g)))) (* (- c e) (+ b (* b f.g))))
                  (= (+ (+ a (+ b (* b f.g))) (* d (+ b (* b f.g)))) (* (- (+ c 1) e) (+ b (* b f.g))))
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
    """.stripMargin,
    """
      (declare-const c1 Int)
      (declare-const c2 Int)
      (declare-const c3 Int)
      (declare-const c4 Int)
      (declare-const c5 Int)
      (declare-const c6 Int)
      (declare-const c7 Int)
      (assert (= c3 (+ c1 c2)))
      (assert (= c3 c6))
      (assert (= c3 1))
      (assert (= c6 1))
      (assert (= c7 (* c6 1000)))
      (assert (= c7 c4))
      (assert (= c7 c5))
      (assert (>= c1 0))
      (assert (>= c2 0))
      (assert (>= c3 0))
      (assert (>= c4 0))
      (assert (>= c5 0))
      (assert (>= c6 0))
      (assert (>= c7 0))
      (maximize (- (+ c1 c4) c5))
      (check-sat)
      (get-objectives)
    """.stripMargin
  )

  queries.foreach(s => println(InvSolver.parseStringAndCheck(s)))


  // println(InvSolver.parseFileAndCheck(Utils.DESKTOP_PATH + "/z3_capability.txt"))
}