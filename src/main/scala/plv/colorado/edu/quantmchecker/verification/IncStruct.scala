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
}