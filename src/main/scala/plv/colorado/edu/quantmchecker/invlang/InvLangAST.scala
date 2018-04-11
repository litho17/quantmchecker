package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangAST

case class SelfAST(id: List[String]) extends InvLangAST

case class RemainderAST(variable: String) extends InvLangAST

case class LineCounterAST(id: String) extends InvLangAST

case class Invariant(remainder: String, self: List[String], posLine: List[String], negLine: List[String]) extends InvLangAST {
  override def toString: String = {
    val selfStr = {
      if (self.isEmpty)
        "<self>"
      else
        self.tail.foldLeft("<self>")((acc, e) => acc + "." + e)
    }
    remainder + "+" +
      selfStr + "=" +
      posLine.foldLeft("")((acc, p) => acc + "+" + p) +
      negLine.foldLeft("")((acc, n) => acc + "-" + n)
  }
}

case class InvNoRem(self: List[String], posLine: List[String], negLine: List[String]) extends InvLangAST {
  override def toString: String = {
    val selfStr = {
      if (self.isEmpty)
        "<self>"
      else
        self.tail.foldLeft("<self>")((acc, e) => acc + "." + e)
    }
    "+" + selfStr + "=" +
      posLine.foldLeft("")((acc, p) => acc + "+" + p) +
      negLine.foldLeft("")((acc, n) => acc + "-" + n)
  }
}