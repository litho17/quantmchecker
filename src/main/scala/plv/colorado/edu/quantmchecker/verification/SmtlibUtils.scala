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
  @deprecated
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

  @deprecated
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
    * @param str an SMTLIB2 string
    * @param token a target string
    * @return if the SMTLIB2 string contains the token
    */
  def containsToken(str: String, token: String): Boolean = {
    parseSmtlibToToken(str).exists {
      case t: SymbolLit => t.content == token
      case _ => false
    }
  }

  /**
    *
    * @param str an SMTLIB2 string
    * @param token a target string
    * @return a set of strings in the SMTLIB2 string, each of which starts with the token
    */
  def startsWithToken(str: String, token: String): HashSet[String] = {
    parseSmtlibToToken(str).foldLeft(new HashSet[String]) {
      (acc, t) => t match {
        case t: SymbolLit => if (t.content.startsWith(token)) acc + t.content else acc
        case _ => acc
      }
    }
  }

  /**
    *
    * @param str a SMTLIB2 string that is a linear expression, e.g. - (+ c2 c3) (- c5 c6)
    * @return a linear expression in Java ILP
    */
  @deprecated
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
        t.kind match {
          case SymbolLitKind =>
            if (!reserved.contains(t.asInstanceOf[SymbolLit].content))
              acc + t.toString
            else {
              // println("Discarded symbol: " + t)
              acc
            }
          case NumeralLitKind | OParen | CParen => acc
          case x@_ => println("Discarded symbol: " + x); acc // discarded
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

  /**
    *
    * @param p
    * @param q
    * @return an SMTLIB2 string: for all free variables in p and q, p => q
    */
  def genImplyQuery(p: String, q: String): String = {
    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"

    val syms = extractSyms(p) ++ extractSyms(q)
    val intTypSyms = syms.foldLeft("") {
      (acc, sym) => acc + " (" + sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypSyms + ")\n"

    prefix + defSyms + implies + "\t\t\t" + p + "\n" + "\t\t\t" + q + suffix
  }

  /**
    *
    * @param p    the SMTLIB2 string representing the size of a list
    * @param _old tokens in p
    * @param _new new tokens that replace old tokens in p
    * @param inc  the increment of the list
    * @param cons additional constraints that help proving the query
    * @return a SMTLIB2 query
    */
  @deprecated
  def genFullQuery(p: String,
                   _old: List[String],
                   _new: List[String],
                   inc: String,
                   cons: Iterable[String]): String = {
    val ret =
      """
        (assert
          (forall (? Int) (? Int) ... )
          (implies
            (and (= LLL p) (cons))
            (= (+ LLL inc) (p[old/new])))
          )
        )
      """.stripMargin

    val q = SmtlibUtils.substituteStmlib(p, _old, _new)

    val uniqueSym = "LLL"
    assert(!p.contains(uniqueSym) && !q.contains(uniqueSym)) // this symbol has to be unique
    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"
    val _p = {
      val tmp = "(= " + uniqueSym + " " + p + ")"
      if (cons.nonEmpty)
        "(and " + tmp + " " + genAndSmtlibStr(cons) + ")"
      else
        tmp
    }
    val _q = {
      val update = "(+ " + uniqueSym + " " + inc + ")"
      "(= " + update + " " + q + ")"
    }
    val syms = extractSyms(_p) ++ extractSyms(_q)
    val intTypedSyms = syms.foldLeft("") {
      (acc, sym) => acc + " (" + sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypedSyms + ")\n"

    prefix + defSyms + implies + "\t\t\t" + _p + "\n" + "\t\t\t" + _q + suffix
  }

  /**
    *
    * @param coefficient the coefficient that describes the size of a list
    * @param inc         the increment of the list
    * @param cons        additional constraints that help proving the query
    * @return a SMTLIB2 query
    */
  @deprecated
  def genPartialQuery(coefficient: String,
                      inc: String,
                      cons: Iterable[String]): String = {
    val ret =
      """
        (assert
          (forall (? Int) (? Int) ... )
           (implies
            cons
            (= (* 1 coefficient) inc)
           )
         )
        )
      """.stripMargin

    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"
    val _p = {
      if (cons.nonEmpty)
        genAndSmtlibStr(cons)
      else
        "true"
    }

    val _q = {
      val lhs = "(* 1 " + smtlibAddParen(coefficient) + ")"
      "(= " + lhs + " " + inc + ")"
    }
    val syms = {
      val uniqueSym = "LLL"
      if (cons.nonEmpty) {
        cons.foldLeft(new HashSet[String]) {
          (acc, s) => acc ++ extractSyms(s)
        }
      } else {
        assert(!_p.contains(uniqueSym) && !_q.contains(uniqueSym)) // this symbol has to be unique
        HashSet(uniqueSym)
      }
    }
    val intTypedSyms = syms.foldLeft("") {
      (acc, sym) => acc + " (" + sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypedSyms + ")\n"
    prefix + defSyms + implies + "\t\t\t" + _p + "\n" + "\t\t\t" + _q + suffix
  }

  def genOpSmtlibStr(str: Iterable[String], op: String): String = {
    if (str.isEmpty) {
      "0"
    } else if (str.size == 1) {
      str.head
    } else {
      str.foldLeft("(" + op){
        (acc, s) => acc + " " + s
      } + ")"
    }
  }
}
