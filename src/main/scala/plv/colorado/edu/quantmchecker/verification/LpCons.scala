package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp.Linear

import scala.collection.immutable.HashSet
import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
case class LpCons(cons: Linear, op: String, rhs: Number)

object LpCons {
  def getVars(c: LpCons): Set[String] = {
    c.cons.getVariables.asScala.foldLeft(new HashSet[String]) {
      (acc, v) => acc + v.toString
    }
  }
}