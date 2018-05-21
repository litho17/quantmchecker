package plv.colorado.edu.quantmchecker.verification

/**
  * @author Tianhan Lu
  */
object TestCases {
  val queries: List[String] = List[String](
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
      (assert
             (forall
               ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
               (implies
                 (= a (* (- c e d) (+ b (* b f))))
                 (= a (* (- c (+ e 1) (- d 1)) (+ b (* b f))))
               )
             )
      )
      (check-sat)
    """.stripMargin,
    """
      |(assert
      |       (forall
      |         ((this.text Int) (i Int) (tagsList Int))
      |         (implies
      |           (and (= i tagsList) (= tagsList this.text))
      |           (=
      |             (+ (* 2 this.text) 1)
      |             (* (+ 1 (+ i i)) 1)
      |           )
      |         )
      |       )
      )
      |(check-sat)
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

  val counters: List[String] = List(
    "- (+ c1 c4) c5",
    "- (+ c2 c3) (- c5 c6)",
    "- (+ c104 c108 c113) (+ c110 c110)",
    "c151"
  )

  val remainders: List[String] = List(
    "+ r1 r2 r3"
  )

  val coefficients: List[String] = List(
    "(* (- ee f) (* (+ e b) (- c d)))"
  )

  val selfIncrement: List[(Array[String], Array[String], Array[String], String)] = List(
    (
      Array("- (+ c104 c108 c113) (+ c110 c110)", "+ i i", "1", "= i tagsList", "= tagsList this.text"),
      Array("- loop c104", "- loop c108", "- loop c110", "- c113 ONE", "- loop ONE"),
      Array("- c134 c135", "it", "+ (* 2 this.text) 1", "= it templateds"),
      "c134"
    ),
    (
      Array("c151", "", "1"),
      Array("- c151 ONE"),
      Array("- c65 c66", "matcher", "1", "= matcher this.text", "= c65 c66"),
      "c65"
    )
  )
}