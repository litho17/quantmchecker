package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangAST

case class SelfAST(_this: String, members: List[String]) extends InvLangAST {
  override def toString: String = {
    members.foldLeft(_this)((acc, member) => acc + "." + member)
  }
}

case class RemainderAST(_this: String, members: List[String]) extends InvLangAST {
  override def toString: String = {
    members.foldLeft(_this)((acc, member) => acc + "." + member)
  }
}

case class LineCounterAST(id: String) extends InvLangAST {
  override def toString: String = id
}

case class Invariant(remainders: List[RemainderAST], selfs: List[SelfAST], posLines: List[String], negLines: List[String]) extends InvLangAST {
  override def toString: String = {
    selfs.foldLeft("")((acc, self) => acc + "+" + self) +
      "=" +
      remainders.foldLeft("")((acc, remainder) => acc + "-" + remainder) +
      posLines.foldLeft("")((acc, p) => acc + "+" + p) +
      negLines.foldLeft("")((acc, n) => acc + "-" + n)
  }
}