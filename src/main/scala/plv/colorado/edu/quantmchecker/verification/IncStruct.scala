package plv.colorado.edu.quantmchecker.verification

/**
  * @author Tianhan Lu
  */
case class IncStruct(counters: String, remainders: String, coefficient: String, remCons: Array[String])

object IncStruct {
  def genIncStruct(str: Array[String]): IncStruct = {
    assert(str.length >= 3)
    IncStruct(str(0), str(1), str(2), str.drop(3))
  }

  /**
    *
    * @param incStruct a struct representing user annotation for a list,
    *                  including counters, remainders and coefficient
    * @param increment the amount of increment that is extracted from counter annotations
    * @return a SMTLIB2 string that describes the increment of list (by taking into
    *         consideration the counter increment)
    */
  def genSmtlibStr(incStruct: IncStruct, increment: Int): String = {
    val lhs = {
      if (incStruct.remainders.nonEmpty)
        "(- " + increment + " " + SmtUtils.addParen(incStruct.remainders) + ") "
      else
        increment + " "
    }
    "(* " + lhs + SmtUtils.addParen(incStruct.coefficient) + ")"
  }

  def genSmtlibStr(incStruct: IncStruct): String = {
    val lhs = "(- " + SmtUtils.addParen(incStruct.counters) + " " + SmtUtils.addParen(incStruct.remainders) + ")"
    val rhs = SmtUtils.addParen(incStruct.coefficient)
    "(* " + lhs + " " + rhs + ")"
  }
}