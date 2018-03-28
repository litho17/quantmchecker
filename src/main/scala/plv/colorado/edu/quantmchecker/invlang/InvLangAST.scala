package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangAST

case class SelfAST(id: List[String]) extends InvLangAST
case class RemainderAST(variable: String) extends InvLangAST
case class LinecounterAST(number: Int) extends InvLangAST

case class Inv(remainder: String, self: List[String], posLine: List[Int], negLine: List[Int]) extends InvLangAST
case class InvNoRem(self: List[String], posLine: List[Int], negLine: List[Int]) extends InvLangAST