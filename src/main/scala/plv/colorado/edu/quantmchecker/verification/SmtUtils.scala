package plv.colorado.edu.quantmchecker.verification

import java.io.StringReader

import plv.colorado.edu.Utils
import smtlib.lexer.Tokens._
import smtlib.trees.Commands.Command

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
  val GET_MODEL = "(get-model)"
  val GET_OBJECTIVES = "(get-objectives)"
  val INIT = "init"
  val ASSERT = "assert"
  val DECL_CONST = "declare-const"
  val MAXIMIZE = "maximize"
  val ASSERT_FALSE = "(assert false)"
  val ASSERT_TRUE = "(assert true)"

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
    * @param str    an SMTLIB2 string
    * @param _old   a list of old tokens
    * @param _new   a list of new tokens
    * @param prefix if also substitute for tokens that are prefixed by any old token
    * @return Simultaneously replace every old token in the SMTLIB2 string with a corresponding new one
    */
  def substitute(str: String, _old: List[String], _new: List[String], prefix: Boolean = false): String = {
    assert(_old.size == _new.size)
    val filter = _old.zip(_new).filter { case (o, n) => o != "" && n != "" } // Filter out ""
    val __old = filter.map { case (o, n) => o }
    val __new = filter.map { case (o, n) => n }
    val tokens = parseSmtlibToToken(str)

    val newTokens: List[Token] = tokens.zipWithIndex.map {
      case (t: SymbolLit, tokenIdx) =>
        val oldTokenIdx = __old.indexOf(t.content)
        if (oldTokenIdx != -1) SymbolLit(__new(oldTokenIdx)) // Exact match
        else if (prefix) { // If prefix match
          val oldTokenIdx = {
            val idxSet = _old.zipWithIndex.filter {
              case (oldToken, _) => t.content.startsWith(oldToken)
            }.map { case (s, i) => i }
            if (idxSet.nonEmpty) idxSet.head else -1 // Only pick the first old token to substitute
          }
          if (oldTokenIdx != -1) {
            assert(oldTokenIdx >= 0)
            val newToken = __new(oldTokenIdx) + t.content.substring(__old(oldTokenIdx).length)
            SymbolLit(newToken)
          } else t
        } else t
      case x@_ => x._1
    }
    // tokens.foreach(t => println(t, t.getClass))
    // newTokens.foreach(t => println(t, t.getClass))
    val ret =
    {
      newTokens.foldLeft("") {
        (acc, t) =>
          if (t.kind == OParen)
            acc + "("
          else if (t.kind == CParen)
            acc + ") "
          else
            acc + t.toString() + " "
      }.trim
    }
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

  def mkAdd(list: String*): String = {
    if (list.isEmpty) "0"
    else if (list.size == 1) list.head
    else list.foldLeft("(+")((acc, a) => acc + " " + addParen(a)) + ")"
  }

  def mkSub(list: String*): String = {
    if (list.isEmpty) "0"
    else if (list.size == 1) list.head
    else list.foldLeft("(-")((acc, a) => acc + " " + addParen(a)) + ")"
  }

  def mkAnd(list: String*): String = {
    if (list.isEmpty) TRUE
    else if (list.size == 1) list.head
    else list.foldLeft("(and")((acc, a) => acc + " " + addParen(a)) + ")"
  }

  def mkAssertion(p: String): String = "(" + ASSERT + " " + addParen(p) + ")"

  def mkConstDecl(v: String): String = "(" + DECL_CONST + " " + v + " Int)"

  def mkQueries(l: Iterable[String]): String = l.foldLeft("") { (acc, e) => acc + e + "\n" }

  def mkMaximize(p: String): String = "(" + MAXIMIZE + " " + p + ")"

  def mkImply(p: String, q: String): String = "(implies " + p + " " + q + ")"

  /**
    *
    * @param str an SMTLIB2 string
    * @return if the given string represents a line counter
    */
  def isLineCounter(str: String): Boolean = {
    val tokens = parseSmtlibToToken(str)
    if (tokens.length == 1) {
      if (str.length > 1) {
        str.startsWith("c") && str.substring(1).forall(c => c.isDigit)
      } else false
    } else false
  }

  /**
    *
    * @param str a SMTLIB2 string
    * @return a set of symbols in the string
    */
  def extractSyms(str: String): HashSet[String] = {
    val reserved = List("+", "-", "*", "/", "=", "and", TRUE, FALSE, INIT, ASSERT)
    val ignored = List("<=", ">=", "Assert", "-1")
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
                if (!ignored.contains(t.toString())) println("Discarded symbol: " + t.toString())
                acc
              }
            } else acc
          case NumeralLitKind | OParen | CParen | StringLitKind | KeywordKind => acc
          case x@_ => // discarded
            if (!ignored.contains(t.toString())) println("Discarded symbol: " + t.toString()); acc
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

  private def properlyChain(elements: Iterable[String]): String = {
    if (elements.isEmpty) ""
    else {
      val head = elements.head
      if (elements.size == 1) elements.head
      else elements.foldLeft(head) {
        (acc, element) => acc + " " + element
      }
    }
  }

  /**
    *
    * @param p an SMTLIB2 string
    * @return assert that for all free variables in the query,
    *         if they are all non-negative, then the query holds
    */
  def mkForall(p: String): String = {
    val prefix = "(assert\n\t(forall\n"
    val suffix = "\n\t)\n)"

    val syms = {
      val syms = extractSyms(p)
      if (syms.isEmpty) syms + "DUMMY" else syms
    }
    val intTypSyms = properlyChain(syms.map(sym => "(" + sym + " Int)"))
    val defSyms = "\t\t(" + intTypSyms + ")\n"
    val nonNegative = mkAnd(syms.map(sym => mkGe(sym, Utils.ZERO_STR)).toArray: _*)

    prefix + defSyms + "\t\t" + addParen(mkImply(nonNegative, addParen(p))) + suffix
  }

  /**
    *
    * @param p
    * @param q
    * @return an SMTLIB2 string: for all free variables in p and q,
    *         if they are all non-negative, then p => q
    */
  def mkForallImply(p: String, q: String): String = {
    if (p == q) return TRUE
    val prefix = "(assert\n\t(forall\n"
    val implies = "\t\t(implies\n"
    val suffix = "\n\t\t)\n\t)\n)"

    val syms = {
      val syms = extractSyms(p) ++ extractSyms(q)
      if (syms.isEmpty) syms + "DUMMY" else syms
    }
    val intTypSyms = properlyChain(syms.map(sym => "(" + sym + " Int)"))
    val defSyms = "\t\t(" + intTypSyms + ")\n"
    val nonNegative = mkAnd(syms.map(sym => mkGe(sym, Utils.ZERO_STR)).toArray: _*)

    prefix + defSyms + implies + "\t\t\t" + addParen(mkAnd(p, nonNegative)) + "\n" + "\t\t\t" + addParen(q) + suffix
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
