package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}
import smtlib.trees.Commands.Assert
import smtlib.trees.Terms.{FunctionApplication, Term}

/**
  * @author Tianhan Lu
  */
class SmtlibParseUnitTest extends FlatSpec with Matchers {
  "parser" should "work" in {
    TestCases.counters.foreach {
      str =>
        VerifyUtils.parseSmtlibToAST("(assert (" + str + "))").foreach {
          case Assert(term: Term) =>
            // println(term, term.getClass)
            term match {
              case app: FunctionApplication =>
                println(app.fun, app.terms)
              case _ =>
            }
          case _ =>
        }
    }
  }
}
