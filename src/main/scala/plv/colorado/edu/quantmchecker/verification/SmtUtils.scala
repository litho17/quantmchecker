package plv.colorado.edu.quantmchecker.verification

import java.io.StringReader

import net.sf.javailp._
import plv.colorado.edu.Utils
import smtlib.lexer.Tokens._
import smtlib.trees.Commands.{Assert, Command, DeclareFun}
import smtlib.trees.Terms.{FunctionApplication, QualifiedIdentifier, Term}

import scala.collection.immutable.HashSet
import scala.collection.mutable.ListBuffer

/**
  * @author Tianhan Lu
  */
object SmtUtils {
  val ONE = "ONE" // Used in annotations to replace (= c7 1) with (- c7 ONE)
  val TRUE = "true"
  val FALSE = "false"
  val SELF = "self"
  val CHECK_SAT = "(check-sat)"
  val INIT = "init"
  val ASSERT = "assert"
  val DECL_CONST = "declare-const"

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
    * @param str    an SMTLIB2 string
    * @param _old   a list of old tokens
    * @param _new   a list of new tokens
    * @param prefix if also substitute for tokens that are prefixed by any old token
    * @return replace every old token in the SMTLIB2 string with a corresponding new one
    */
  def substitute(str: String, _old: List[String], _new: List[String], prefix: Boolean = false): String = {
    assert(_old.size == _new.size)
    val filter = _old.zip(_new).filter { case (o, n) => o != "" && n != "" } // Filter out ""
    val __old = filter.map { case (o, n) => o }
    val __new = filter.map { case (o, n) => n }
    val tokens = parseSmtlibToToken(str)

    def _substitute(tokenIdx: Int, oldToken: Token, newToken: Token): Token = {
      if (tokenIdx >= 1) { // TODO: Don't replace any arg of init (hard coded)
        if (tokens(tokenIdx - 1).toString() == INIT) oldToken else newToken
      } else newToken
    }

    val newTokens = tokens.zipWithIndex.map {
      case (t: SymbolLit, tokenIdx) =>
        val oldTokenIdx = __old.indexOf(t.content)
        if (oldTokenIdx != -1) _substitute(tokenIdx, t, SymbolLit(__new(oldTokenIdx)))
        else if (prefix) {
          val oldTokenIdx = {
            val idxSet = _old.zipWithIndex.filter {
              case (oldToken, _) => t.content.startsWith(oldToken)
            }.map { case (s, i) => i }
            if (idxSet.nonEmpty) idxSet.head else -1 // Only pick the first old token to substitute
          }
          if (oldTokenIdx != -1) {
            assert(oldTokenIdx >= 0)
            val newToken = __new(oldTokenIdx) + t.content.substring(__old(oldTokenIdx).length)
            _substitute(tokenIdx, t, SymbolLit(newToken))
          } else t
        } else t
      case x@_ => x._1
    }
    // tokens.foreach(t => println(t, t.getClass))
    // newTokens.foreach(t => println(t, t.getClass))
    val ret = newTokens.foldLeft("") {
      (acc, t) =>
        if (t.kind == OParen)
          acc + "( "
        else if (t.kind == CParen)
          acc + ") "
        else
          acc + t.toString() + " "
    }.trim
    rmParen(ret)
  }

  /**
    *
    * @param str   an SMTLIB2 string
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
    * @param str   an SMTLIB2 string
    * @param token a target string
    * @return a set of strings in the SMTLIB2 string, each of which starts with the token
    */
  def startsWithToken(str: String, token: String): HashSet[String] = {
    parseSmtlibToToken(str).foldLeft(new HashSet[String]) {
      (acc, t) =>
        t match {
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
      if (str.contains(" ")) "(" + ASSERT + " (" + str + "))" // e.g. - (+ c2 c3) (- c5 c6)
      else "(declare-fun " + str + " () Int)" // e.g. c151
    }
    // println(transformedStr)
    val cmds = SmtUtils.parseSmtlibToAST(transformedStr)
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

  def addParen(str: String): String = {
    if (str.contains(" ") && !str.startsWith("("))
      "(" + str + ")"
    else
      str
  }

  def rmParen(str: String): String = {
    val ret = str.trim
    if (ret.startsWith("(") && ret.endsWith(")")) ret.substring(1, ret.length - 1) else ret.trim
  }

  def mkGe(a: String, b: String): String = "(>= " + addParen(a) + " " + addParen(b) + ")"

  def mkGt(a: String, b: String): String = "(> " + addParen(a) + " " + addParen(b) + ")"

  def mkLe(a: String, b: String): String = "(<= " + addParen(a) + " " + addParen(b) + ")"

  def mkLt(a: String, b: String): String = "(< " + addParen(a) + " " + addParen(b) + ")"

  def mkEq(a: String, b: String): String = "(= " + addParen(a) + " " + addParen(b) + ")"

  def mkAdd(list: String*): String = list.foldLeft("(+")((acc, a) => acc + " " + addParen(a)) + ")"

  def mkSub(list: String*): String = list.foldLeft("(-")((acc, a) => acc + " " + addParen(a)) + ")"

  def mkAnd(list: String*): String = list.foldLeft("(and")((acc, a) => acc + " " + addParen(a)) + ")"

  def mkAssertion(p: String): String = "(" + ASSERT + " " + addParen(p) + ")"

  def mkDeclConst(v: String): String = "(" + DECL_CONST + " " + v + " Int)"

  def mkQueries(l: Iterable[String]): String = l.foldLeft("") { (acc, e) => acc + e + "\n" }

  /**
    *
    * @param str an SMTLIB2 string
    * @return if the given string represents a line counter
    */
  def isLineCounter(str: String): Boolean = {
    val tokens = parseSmtlibToToken(str)
    if (tokens.length == 1) {
      if (str.length >= 1) {
        str.startsWith("c") && str.substring(1).forall(c => c.isDigit)
      } else false
    } else false
  }

  /**
    *
    * @param inv an invariant
    * @return if the invariant is composed of only 1 token, then return "= self inv"
    */
  def invToSMTLIB2(inv: String): String = {
    val tokens = parseSmtlibToToken(inv)
    if (tokens.length == 1) {
      val token = tokens.head.toString()
      if (token == SELF) {
        assert(false, "Invariant cannot be self")
        TRUE
      } else if (token != TRUE && token != FALSE) { // Automatically tranform invariant (e.g. x|n|c -> = self x|n|c)
        rmParen(mkEq(SELF, inv)) // Note that parenthesis are removed
      } else
        inv
    } else
      inv
  }

  /**
    *
    * @param inv an invariant
    * @return if the invariant is form "= self a", then return "a"
    */
  def SMTLIB2Toinv(inv: String): String = { // TODO: not tested
    val tokens = parseSmtlibToToken(inv)
    if (tokens.length == 3) {
      if (tokens(1).toString() == SELF) {
        val ret = tokens(2).toString()
        assert(ret != SELF)
        ret
      } else inv
    } else
      inv
  }

  /**
    *
    * @param str a SMTLIB2 string
    * @return a set of symbols in the string
    */
  def extractSyms(str: String): HashSet[String] = {
    val reserved = List("+", "-", "*", "/", "=", "and", TRUE, FALSE, INIT, ASSERT)
    val ignoreDiscarded = List("<=", ">=", "Assert", "-1")
    parseSmtlibToToken(str).foldLeft(new HashSet[String]) {
      (acc, t) =>
        t.kind match {
          case SymbolLitKind =>
            val content = t.toString()
            if (!reserved.contains(content)) { // Get rid of e.g. "-1", "*"
              val isValidId = Utils.isValidId(content)
              val isValidDotExpr = { // Also extract valid dot expressions (e.g. v.g, self.f)
                if (content.contains(".")) content.split(".").forall(s => Utils.isValidId(s))
                else false
              }
              if (isValidDotExpr || isValidId) acc + content
              else {
                if (!ignoreDiscarded.contains(t.toString())) println("Discarded symbol: " + t.toString())
                acc
              }
            } else acc
          case NumeralLitKind | OParen | CParen | StringLitKind | KeywordKind => acc
          case x@_ => // discarded
            if (!ignoreDiscarded.contains(t.toString())) println("Discarded symbol: " + t.toString()); acc
        }
    }
  }

  /**
    *
    * @param c a list of SMTLIB2 constraints
    * @return the conjunction of all of the constraints
    */
  def conjunctionAll(c: Iterable[String]): String = {
    if (c.isEmpty) {
      TRUE
    } else if (c.size == 1) {
      c.head
    } else {
      c.foldLeft("(and") {
        (acc, c) => acc + " " + addParen(c)
      } + ")"
    }
  }

  /**
    *
    * @param p an SMTLIB2 string
    * @return assert that for all variables in the query, the query holds
    */
  def mkAssertionForall(p: String): String = {
    val prefix = "(assert\n\t(forall\n"
    val suffix = "\n\t)\n)"

    val syms = {
      val syms = extractSyms(p)
      if (syms.isEmpty) syms + "DUMMY" else syms
    }
    val intTypSyms = syms.foldLeft("") {
      (acc, sym) => acc + " (" + sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypSyms + ")\n"

    prefix + defSyms + "\t\t" + addParen(p) + suffix
  }

  /**
    *
    * @param p
    * @param q
    * @return an SMTLIB2 string: for all free variables in p and q, p => q
    */
  def mkImply(p: String, q: String): String = {
    if (p == q) return TRUE
    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"

    val syms = {
      val syms = extractSyms(p) ++ extractSyms(q)
      if (syms.isEmpty) syms + "DUMMY" else syms
    }
    val intTypSyms = syms.foldLeft("") {
      (acc, sym) => acc + " (" + sym + " Int)"
    }
    val defSyms = "\t\t(" + intTypSyms + ")\n"

    prefix + defSyms + implies + "\t\t\t" + addParen(p) + "\n" + "\t\t\t" + addParen(q) + suffix
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

    val q = SmtUtils.substitute(p, _old, _new)

    val uniqueSym = "LLL"
    assert(!p.contains(uniqueSym) && !q.contains(uniqueSym)) // this symbol has to be unique
    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"
    val _p = {
      val tmp = "(= " + uniqueSym + " " + p + ")"
      if (cons.nonEmpty)
        "(and " + tmp + " " + conjunctionAll(cons) + ")"
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
        conjunctionAll(cons)
      else
        "true"
    }

    val _q = {
      val lhs = "(* 1 " + addParen(coefficient) + ")"
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
}
