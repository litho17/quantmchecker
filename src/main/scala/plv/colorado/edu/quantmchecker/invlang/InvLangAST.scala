package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangAST

case class SelfAST(id: List[String]) extends InvLangAST

case class RemainderAST(variable: String) extends InvLangAST

case class LinecounterAST(number: Int) extends InvLangAST

case class Inv(remainder: String, self: List[String], posLine: List[Int], negLine: List[Int]) extends InvLangAST {
  override def toString: String = {
    remainder + " + " +
      self.tail.foldLeft(self.head)((acc, e) => acc + "." + e) + " = " +
      posLine.foldLeft("")((acc, p) => acc + " + " + p) +
      negLine.foldLeft("")((acc, n) => acc + " - " + n)
  }
}

case class InvNoRem(self: List[String], posLine: List[Int], negLine: List[Int]) extends InvLangAST {
  override def toString: String = {
    "+" + self.tail.foldLeft(self.head)((acc, e) => acc + "." + e) + " = " +
      posLine.foldLeft("")((acc, p) => acc + " + " + p) +
      negLine.foldLeft("")((acc, n) => acc + " - " + n)
  }
}