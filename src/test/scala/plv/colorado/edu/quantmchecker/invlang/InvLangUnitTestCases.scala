package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvLangUnitTestCases {
  val lexerTests = List(
    "500",
    "=",
    "+",
    "+x.f+y.g+z.e.f/=+c10+c29+c41-c11"
  )

  val parserTests = List(
    "+z.e.f/=-x.f-y.g+c10+c29+c41-c11",
    "+z.e.f/=+c10+c29+c41-c11"
  )
}
