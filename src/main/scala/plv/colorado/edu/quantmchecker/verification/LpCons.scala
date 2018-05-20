package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp.Linear

/**
  * @author Tianhan Lu
  */
case class LpCons(cons: Linear, op: String, rhs: Number)
