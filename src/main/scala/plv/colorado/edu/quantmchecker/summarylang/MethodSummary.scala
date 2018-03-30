package plv.colorado.edu.quantmchecker.summarylang

/**
  * @author Tianhan Lu
  */

sealed trait MethodSummary
case class MethodSummaryI(variable: String, increment: Integer) extends MethodSummary
case class MethodSummaryV(variable: String, increment: String) extends MethodSummary

// case class MethodSummaries(summaries: List[MethodSummary])
