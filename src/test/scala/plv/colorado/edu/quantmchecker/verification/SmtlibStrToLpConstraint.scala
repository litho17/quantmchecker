package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}
import smtlib.trees.Commands.Assert
import smtlib.trees.Terms.{FunctionApplication, Term}

/**
  * @author Tianhan Lu
  */
class SmtlibStrToLpConstraint extends FlatSpec with Matchers {
  "lp constraint generation" should "be successful" in {
    TestCases.counters.foreach {
      str =>
        VerifyUtils.parseSmtlibStr("(assert (" + str + "))").foreach {
          case Assert(term: Term) =>
            // println(term, term.getClass)
            term match {
              case app: FunctionApplication =>
                println(app.fun, app.terms)
                val linearCons = VerifyUtils.toLinearCons(VerifyUtils.linearPrefixToInfix(app))
                println(linearCons)
              case _ =>
            }
          case _ =>
        }
    }
  }
}
