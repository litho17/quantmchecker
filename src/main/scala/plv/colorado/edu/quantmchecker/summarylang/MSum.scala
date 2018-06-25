package plv.colorado.edu.quantmchecker.summarylang

/**
  * @author Tianhan Lu
  */

sealed trait MSum
case class MSumI(variable: String, increment: Integer) extends MSum {
  override def toString: String = "@Summary(" + variable + ": " + increment + ")"
}
case class MSumV(variable: String, increment: String) extends MSum {
  override def toString: String = "@Summary(" + variable + ": " + increment + ")"
}