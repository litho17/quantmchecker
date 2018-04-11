package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvLangUnitTestCases {
  val lexerTests = List(
    "500",
    "=",
    "+",
    "x+<self>.e.f=+c10+c29+c41-c11"
  )

  val parserTests = List(
    "x+<self>.e.f=+c10+c29+c41-c11",
    "+<self>.e.f=+c10+c29+c41-c11",
    "sortedWCs+<self>=+WordStatsProcessor22+WordStatsProcessor23+WordStatsProcessor24+WordStatsProcessor25+WordFrequencyProcessor32-WordFrequencyProcessor31"
  )
}
