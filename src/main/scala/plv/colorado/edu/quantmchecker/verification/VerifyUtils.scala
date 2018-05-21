package plv.colorado.edu.quantmchecker.verification

import java.io.StringReader

import com.sun.source.tree._
import net.sf.javailp._
import smtlib.lexer.Tokens.{CParen, OParen, SymbolLit, Token}
import smtlib.trees.Commands.Command
import smtlib.trees.Terms.{FunctionApplication, QualifiedIdentifier}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet
import scala.collection.mutable.ListBuffer

/**
  * @author Tianhan Lu
  */
object VerifyUtils {
  val DEFAULT_LOOP_BOUND = 1000

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

  private def genEqCons(stmts: Set[Tree]): Set[Linear] = {
    if (stmts.nonEmpty) {
      val headHashcode = stmts.head.hashCode().toString
      stmts.tail.foldLeft(new HashSet[Linear]) {
        (acc, s) =>
          val cons = new Linear // head = s1, head = s2, ...
          cons.add(-1, headHashcode)
          cons.add(1, s.hashCode().toString)
          acc + cons
      }
    } else
      new HashSet[Linear]
  }

  def treeToCons(tree: CaseTree): Set[Linear] = genEqCons(tree.getStatements.asScala.toSet + tree)

  def treeToCons(tree: CatchTree): Set[Linear] = genEqCons(tree.getBlock.getStatements.asScala.toSet + tree)

  /**
    *
    * @param tree a statement tree (AST node)
    * @return a set of linear constraints that describe the control flow relations inside the target AST node
    */
  def treeToCons(tree: StatementTree): Set[Linear] = {
    if (tree == null)
      return new HashSet[Linear]

    def genLoopCons(loop: StatementTree, body: StatementTree): Set[Linear] = {
      if (loop.isInstanceOf[DoWhileLoopTree] || loop.isInstanceOf[EnhancedForLoopTree] || loop.isInstanceOf[WhileLoopTree]) {
        val cons = new Linear // DEFAULT_LOOP_BOUND * this = block
        cons.add(-DEFAULT_LOOP_BOUND, loop.hashCode().toString)
        cons.add(1, body.hashCode().toString)
        treeToCons(body) + cons
      } else
        new HashSet[Linear]
    }

    val thisHashcode = tree.hashCode().toString
    tree match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(genEqCons(stmt.getStatements.asScala.toSet + stmt)) {
          (acc, s) => acc ++ treeToCons(s)
        }
      case stmt: DoWhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: EnhancedForLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: WhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: ForLoopTree =>
        val initCons = genEqCons(stmt.getInitializer.asScala.toSet + tree) // this = init1 = init2 = ...
      val cons = new Linear // DEFAULT_LOOP_BOUND * this = block
        cons.add(-DEFAULT_LOOP_BOUND, thisHashcode)
        cons.add(1, stmt.getStatement.hashCode().toString)
        initCons ++ treeToCons(stmt.getStatement) + cons
      case stmt: LabeledStatementTree =>
        val cons1 = new Linear // this = body
        cons1.add(-1, thisHashcode)
        cons1.add(1, stmt.getStatement.hashCode().toString)

        val cons2 = new Linear // this = label
        cons2.add(-1, thisHashcode)
        cons2.add(1, stmt.getLabel.toString)

        treeToCons(stmt.getStatement) + cons1 + cons2
      case stmt: IfTree =>
        val cons = new Linear // this = then + else
        cons.add(-1, thisHashcode)
        cons.add(1, stmt.getThenStatement.hashCode().toString)
        if (stmt.getElseStatement != null)
          cons.add(1, stmt.getElseStatement.hashCode().toString)
        treeToCons(stmt.getThenStatement) ++ treeToCons(stmt.getElseStatement) + cons
      case stmt: SwitchTree =>
        val cons = new Linear // this = case1 + case2 + ...
        cons.add(-1, thisHashcode)
        stmt.getCases.asScala.foreach(casetree => cons.add(1, casetree.hashCode().toString))
        stmt.getCases.asScala.foldLeft(HashSet[Linear](cons)) {
          (acc, casetree) => acc ++ treeToCons(casetree)
        }
      case stmt: ExpressionStatementTree => new HashSet[Linear]
      case stmt: ReturnTree => new HashSet[Linear]
      case stmt: VariableTree => new HashSet[Linear]
      case stmt: TryTree =>
        val cons1 = new Linear // this = try
        cons1.add(-1, thisHashcode)
        cons1.add(1, stmt.getBlock.hashCode().toString)
        val cons2 = new Linear // this = finally
        if (stmt.getFinallyBlock != null) {
          cons2.add(-1, thisHashcode)
          cons2.add(1, stmt.getFinallyBlock.hashCode().toString)
        }
        val cons3 = new Linear // this = catch1 + catch2 + ...
        cons3.add(-1, thisHashcode)
        stmt.getCatches.asScala.foreach(catchtree => cons3.add(1, catchtree.hashCode().toString))
        stmt.getCatches.asScala.foldLeft(HashSet[Linear](cons1, cons2, cons3)) {
          (acc, catchtree) => acc ++ treeToCons(catchtree)
        } ++ treeToCons(stmt.getBlock) ++ treeToCons(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => treeToCons(stmt.getBlock)
      case _ => new HashSet[Linear]
    }
  }

  /**
    *
    * @param methodTree a method
    * @param obj        an optimization object
    * @return max value of the object under the constraints generated from the method
    */
  def optimizeWithinMethod(methodTree: MethodTree, obj: Linear): Option[Result] = {
    val cons1 = treeToCons(methodTree.getBody)
    val cons2 = new Linear // body = 1
    if (methodTree.getBody != null)
      cons2.add(1, methodTree.getBody.hashCode().toString)

    val cons: Set[LpCons] = cons1.map(l => LpCons(l, "=", 0)) + LpCons(cons2, "=", 1)

    val vars = cons.foldLeft(new HashSet[String]) {
      (acc, c) =>
        c.cons.getVariables.asScala.foldLeft(acc) {
          (acc2, v) => acc2 + v.toString
        }
    }

    val ifEveryObjVarIsConstrained = obj.getVariables.asScala.forall(v => vars.contains(v.toString))
    if (ifEveryObjVarIsConstrained)
      Some(VerifyUtils.solveLp(cons, obj, vars, classOf[Integer], 0, OptType.MAX))
    else
      None
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
}
