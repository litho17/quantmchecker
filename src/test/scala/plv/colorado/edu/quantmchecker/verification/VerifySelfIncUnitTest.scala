package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp.Linear
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
class VerifySelfIncUnitTest extends FlatSpec with Matchers {
  "increment of self" should "be validated" in {
    TestCases.selfIncrement.foreach {
      x =>
        val calleeStruct = IncStruct.genIncStruct(x._1)
        val callerStruct = IncStruct.genIncStruct(x._3)
        println("counters: " + calleeStruct.counters)
        val obj = VerifyUtils.parseSmtlibStrToLpCons(calleeStruct.counters)
        val one = new Linear
        one.add(1, VerifyUtils.ONE)
        val constraints = x._2.foldLeft(HashSet[LpCons](LpCons(one, "=", 1))) {
          (acc, s) =>
            VerifyUtils.parseSmtlibStrToLpCons(s) match {
              case Some(cons) => acc + LpCons(cons, "=", 0)
              case None => acc
            }
        }
        println("res: " + VerifyUtils.solveLp(constraints, obj))
    }
  }
}
