package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvUtils {
  /**
    *
    * @param invariant
    * @return 1. Remainder's name
    *         2. A list where every element represents a field of <self>, except that the first element is name of the variable that <self> describes
    *         3. The full access path starting from <self>
    *
    */
  def extractInv(invariant: InvLangAST): (String, List[String], String) = {
    invariant match {
      case Invariant(remainder, self, _, _) =>
        (remainder, self, self.tail.foldLeft(self.head)((acc, e) => acc + "." + e))
      case InvNoRem(self, _, _) =>
        ("", self, self.tail.foldLeft(self.head)((acc, e) => acc + "." + e))
      case _ => ("", List.empty, "")
    }
  }
}