package plv.colorado.edu.quantmchecker.verification

import java.io.StringReader

import net.sf.javailp._
import smtlib.lexer.Tokens._
import smtlib.trees.Commands.{Assert, Command, DeclareFun}
import smtlib.trees.Terms.{FunctionApplication, QualifiedIdentifier, Term}

import scala.collection.immutable.HashSet
import scala.collection.mutable.ListBuffer

/**
  * @author Tianhan Lu
  */
object SmtlibUtils {
  val ONE = "ONE" // Used in annotations to replace (= c7 1) with (- c7 ONE)

  /**
    *
    * @param str a SMTLIB2 string
    * @return a list of command
    */
  def parseSmtlibToAST(str: String): List[Command] = {
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

  def parseSmtlibToToken(str: String): List[Token] = {
    val reader = new StringReader(str)
    val lexer = new smtlib.lexer.Lexer(reader)
    var tokens = new ListBuffer[Token]
    var token = lexer.nextToken
    while (token != null) {
      tokens.append(token)
      token = lexer.nextToken
    }
    tokens.toList
  }

  /**
    *
    * @param term a SMTLIB2 linear prefix expression, e.g. (- (+ c1 c4) c5)
    * @return a list of pairs (coefficient and variable name), to be constructed as infix expression
    */
  private def linearPrefixToInfix(term: FunctionApplication): List[(Int, String)] = {
    val subterms: Seq[List[(Int, String)]] = term.terms.map {
      case subterm: FunctionApplication => linearPrefixToInfix(subterm) // recursive case
      case subterm: QualifiedIdentifier => List((1, subterm.toString())) // base case
      case x@_ => println("Discarded term: " + x); List.empty // discarded
    }
    val lhs: List[(Int, String)] = subterms.head
    val rhs: List[(Int, String)] = term.fun.toString() match {
      case "-" =>
        subterms.tail.flatMap {
          subterm: List[(Int, String)] =>
            subterm.map {
              case (num, str) => (-Integer.parseInt(num.toString), str)
            }
        }.toList
      case "+" => subterms.tail.flatten.toList
      case "=" => List.empty
      case x@_ => println("Discarded function: " + x); List.empty // discarded
    }
    lhs ::: rhs // only the first two terms are kept in result
  }

  def toLinearCons(in: List[(Int, String)]): Linear = {
    val res = new Linear
    in.foreach { case (num, str) => res.add(num, str) }
    res
  }

  /**
    *
    * @param str  a SMTLIB2 string
    * @param _old a list of old tokens
    * @param _new a list of new tokens
    * @return replace every old token in the SMTLIB2 string with a corresponding new one
    */
  def substituteStmlib(str: String, _old: List[String], _new: List[String]): String = {
    assert(_old.size == _new.size)
    val tokens = parseSmtlibToToken(str)
    val newTokens = tokens.map {
      case t: SymbolLit =>
        val idx = _old.indexOf(t.content)
        if (idx != -1)
          SymbolLit(_new(idx))
        else
          t
      case x@_ => x
    }
    // tokens.foreach(t => println(t, t.getClass))
    // newTokens.foreach(t => println(t, t.getClass))
    newTokens.foldLeft("") {
      (acc, t) =>
        if (t.kind == OParen)
          acc + "( "
        else if (t.kind == CParen)
          acc + ") "
        else
          acc + t.toString() + " "
    }
  }

  /**
    *
    * @param str a SMTLIB2 string that is a linear expression, e.g. - (+ c2 c3) (- c5 c6)
    * @return a linear expression in Java ILP
    */
  def parseSmtlibStrToLpCons(str: String): Option[Linear] = {
    val transformedStr = {
      if (str.contains(" "))
        "(assert (" + str + "))" // e.g. - (+ c2 c3) (- c5 c6)
      else
        "(declare-fun " + str + " () Int)" // e.g. c151
    }
    // println(transformedStr)
    val cmds = SmtlibUtils.parseSmtlibToAST(transformedStr)
    if (cmds.nonEmpty) {
      cmds.head match {
        case Assert(term: Term) =>
          term match {
            case app: FunctionApplication =>
              // println(app.fun, app.terms)
              Some(toLinearCons(linearPrefixToInfix(app)))
            case _ => None
          }
        case fun: DeclareFun =>
          val l = new Linear
          l.add(1, fun.name.name)
          Some(l)
        case _ => None
      }
    } else
      None
  }

  /**
    *
    * @param str a SMTLIB2 string
    * @return a properly parenthesized SMTLIB2 string
    */
  def smtlibAddParen(str: String): String = {
    if (str.contains(" "))
      "(" + str + ")"
    else
      str
  }

  /**
    *
    * @param str a SMTLIB2 string
    * @return a set of symbols in the string
    */
  def extractSyms(str: String): Set[String] = {
    val reserved = List("+", "-", "*", "/", "=", "and")
    parseSmtlibToToken(str).foldLeft(new HashSet[String]) {
      (acc, t) =>
        t match {
          case t: SymbolLit =>
            if (!reserved.contains(t.content))
              acc + t.toString
            else
              acc
          case x@_ => acc // discarded
        }
    }
  }

  /**
    *
    * @param c a list of SMTLIB2 constraints
    * @return the conjunction of all of the constraints
    */
  def genAndSmtlibStr(c: Iterable[String]): String = {
    c.foldLeft("(and") {
      (acc, c) => acc + " " + smtlibAddParen(c)
    } + ")"
  }

  def genForallImpQuery(p: String,
                        _old: List[String],
                        _new: List[String],
                        inc: String,
                        cons: Iterable[String]): String = {
    val q = SmtlibUtils.substituteStmlib(p, _old, _new)

    val uniqueSym = "LLL"
    assert(!p.contains(uniqueSym) && !q.contains(uniqueSym)) // this symbol has to be unique
    val prefix = "(assert\n\t(forall\n"

    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"
    val _p = "(= " + uniqueSym + " " + p + ")"
    val _q = {
      val update = "(+ " + uniqueSym + " " + inc + ")"
      val inv = "(= " + update + " " + q + ")"
      if (cons.nonEmpty)
        "(and " + inv + " " + genAndSmtlibStr(cons) + ")"
      else
        inv
    }
    val syms = extractSyms(_p) ++ extractSyms(_q)
    val intTypedSyms = syms.foldLeft("") {
      (acc, sym) => acc + " ("  +sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypedSyms + ")\n"

    prefix + defSyms + implies + "\t\t\t" + _p + "\n" + "\t\t\t" + _q + suffix
  }
}
