package plv.colorado.edu.quantmchecker

/**
  * @author Tianhan Lu
  */
object InvLangUnitTestCases {
  val lexerTests = List(
    "500",
    "<=",
    "=",
    "+",
    "*",
    "REM(x1)",
    "REM(x1)*500",
    "REM(x1)500",
    "REM(x1)*500+LIST(y1)",
    "REM(x1)*500+LIST(y1)<=LIMIT(z1)",
    "REM(x1)*500+LIST(y1)<=LIMIT(z1)+_extra"
  )

  val parserTests = List(
    "REM(x1)*500+LIST(y1)<=LIMIT(z1)",
    "REM(x1)*500+LIST(y1)<=LIMIT(z1)+_extra"
  )
}
