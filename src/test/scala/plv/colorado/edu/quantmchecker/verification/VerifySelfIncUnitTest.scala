package plv.colorado.edu.quantmchecker.verification

import net.sf.javailp.Linear
import org.scalatest.{FlatSpec, Matchers}
import plv.colorado.edu.quantmchecker.invlang.InvSolver

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
        // println("counters: " + calleeStruct.counters)
        val obj = SmtUtils.parseSmtlibStrToLpCons(calleeStruct.counters)
        val one = new Linear
        one.add(1, SmtUtils.ONE)
        val constraints = x._2.foldLeft(HashSet[LpCons](LpCons(one, "=", 1))) {
          (acc, s) =>
            SmtUtils.parseSmtlibStrToLpCons(s) match {
              case Some(cons) => acc + LpCons(cons, "=", 0)
              case None => acc
            }
        }
        val maxInc = SolveLP.solveLp(constraints, obj) match {
          case Some(res) => res.getObjective.intValue()
          case None => 0
        }
        val listIncStr = IncStruct.genSmtlibStr(calleeStruct, maxInc)
        val remCons = calleeStruct.remCons.map(s => SmtUtils.parseSmtlibStrToLpCons(s)).foldLeft(new HashSet[LpCons]) {
          (acc, c) =>
            c match {
              case Some(c) => acc + LpCons(c, "=", 0)
              case None => acc
            }
        }
        val _old = List(x._4)
        val _new = List("(+ " + x._4 + " 1)")
        val fullQuery = SmtUtils.genFullQuery(
          IncStruct.genSmtlibStr(callerStruct),
          _old,
          _new,
          listIncStr,
          calleeStruct.remCons
        )
        val partialQuery = SmtUtils.genPartialQuery(
          callerStruct.coefficient,
          listIncStr,
          calleeStruct.remCons
        )
        println(fullQuery, assert(InvSolver.parseStringAndCheck(fullQuery)))
        println(partialQuery, assert(InvSolver.parseStringAndCheck(partialQuery)))

        // println(IncStruct.genSmtlibStr(calleeStruct))
        // println(IncStruct.genSmtlibStr(callerStruct))
        // println(listIncStr)
    }
  }
}
