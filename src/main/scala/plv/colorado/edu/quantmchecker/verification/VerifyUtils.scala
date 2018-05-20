package plv.colorado.edu.quantmchecker.verification

import java.io.StringReader

import net.sf.javailp._
import smtlib.trees.Commands.Command
import smtlib.trees.Terms.{FunctionApplication, QualifiedIdentifier}

import scala.collection.mutable.ListBuffer

/**
  * @author Tianhan Lu
  */
object VerifyUtils {
  /**
    *
    * @param str a SMTLIB2 string
    * @return a list of command
    */
  def parseSmtlibStr(str: String): List[Command] = {
    val reader = new StringReader(str)
    // val is = new java.io.FileReader("INPUT")
    val lexer = new smtlib.lexer.Lexer(reader)
    val parser = new smtlib.parser.Parser(lexer)
    var cmds = new ListBuffer[Command]
    var cmd = parser.parseCommand
    while (cmd != null) {
      cmds.append(cmd)
      cmd = parser.parseCommand
    }
    cmds.toList
  }

  def solveLp[T](constraints: Iterable[LpCons],
                 obj: Linear,
                 vars: Iterable[String],
                 varType: Class[T],
                 lowerBound: Number,
                 optType: OptType): Result = {
    val factory = new SolverFactoryLpSolve()
    factory.setParameter(Solver.VERBOSE, 0)
    factory.setParameter(Solver.TIMEOUT, 100) // set timeout to 100 seconds
    val problem = new Problem()
    constraints.foreach(c => problem.add(c.cons, c.op, c.rhs))
    problem.setObjective(obj, optType)
    vars.foreach(v => problem.setVarType(v, varType))
    vars.foreach(v => problem.setVarLowerBound(v, lowerBound))
    factory.get.solve(problem)
  }

  /**
    *
    * @param term a SMTLIB2 linear prefix expression, e.g. (- (+ c1 c4) c5)
    * @return a list of pairs (coefficient and variable name), to be constructed as infix expression
    */
  def linearPrefixToInfix(term: FunctionApplication): List[(Int, String)] = {
    val subterms: Seq[List[(Int, String)]] = term.terms.map {
      case subterm: FunctionApplication => linearPrefixToInfix(subterm) // recursive case
      case subterm: QualifiedIdentifier => List((1, subterm.toString())) // base case
      case x@_ => println("Discarded term: " + x); List.empty // discarded
    }
    val lhs: List[(Int, String)] = subterms.head
    val rhs: List[(Int, String)] = term.fun.toString() match {
      case "-" => subterms(1).map {
        case (num, str) =>
          (-Integer.parseInt(num.toString), str)
      }
      case "+" => subterms(1)
      case x@_ => println("Discarded function: " + x); List.empty // discarded
    }
    lhs ::: rhs // only the first two terms are kept in result
  }

  def toLinearCons(in: List[(Int, String)]): Linear = {
    val res = new Linear
    in.foreach { case (num, str) => res.add(num, str) }
    res
  }
}
