package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvLangUnitTestCases {
  val lexerTests = List(
    "500",
    "=",
    "+",
    "x+<self>.e.f=+10+29+41-11"
  )

  val parserTests = List(
    "x+<self>.e.f=+10+29+41-11",
    "+<self>.e.f=+10+29+41-11"
  )
}
