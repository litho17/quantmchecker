package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvUtils {
  /**
    *
    * @param invariant
    * @return remainder's name
    *         a list where every element represents a field of <self>
    *
    */
  def getRemSelf(invariant: InvLangAST): (String, List[String], String) = {
    invariant match {
      case Invariant(remainder, self, _, _) =>
        (remainder, self, self.tail.foldLeft(self.head)((acc, e) => acc + "." + e))
      case InvNoRem(self, _, _) =>
        ("", self, self.tail.foldLeft(self.head)((acc, e) => acc + "." + e))
      case _ => ("", List.empty, "")
    }
  }
}