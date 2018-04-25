package plv.colorado.edu.quantmchecker.summarylang

/**
  * @author Tianhan Lu
  */

sealed trait MethodSummary
case class MethodSummaryI(variable: String, increment: Integer) extends MethodSummary {
  override def toString: String = "@Summary(" + variable + ": " + increment + ")"
}
case class MethodSummaryV(variable: String, increment: String) extends MethodSummary {
  override def toString: String = "@Summary(" + variable + ": " + increment + ")"
}

// case class MethodSummaries(summaries: List[MethodSummary])
