package plv.colorado.edu.quantmchecker.verification

import com.sun.source.tree._
import plv.colorado.edu.Utils

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object CFRelation {
  val DEFAULT_LOOP_BOUND = 1000

  private def genEqCons(stmts: Set[Tree]): Set[String] = {
    if (stmts.nonEmpty) {
      val headHashcode = Utils.hashCode(stmts.head)
      stmts.tail.foldLeft(new HashSet[String]) {
        (acc, s) => // head = s1, head = s2, ...
          acc + SmtUtils.mkEq(headHashcode, Utils.hashCode(s))
      }
    } else
      new HashSet[String]
  }

  def treeToCons(tree: CaseTree): Set[String] = genEqCons(tree.getStatements.asScala.toSet + tree)

  def treeToCons(tree: CatchTree): Set[String] = genEqCons(tree.getBlock.getStatements.asScala.toSet + tree)

  /**
    *
    * @param tree a statement tree (AST node)
    * @return a set of String constraints that describe the control flow relations inside the target AST node
    */
  def treeToCons(tree: StatementTree): Set[String] = {
    if (tree == null)
      return new HashSet[String]

    def genLoopCons(loop: StatementTree, body: StatementTree): Set[String] = {
      if (loop.isInstanceOf[DoWhileLoopTree] || loop.isInstanceOf[EnhancedForLoopTree] || loop.isInstanceOf[WhileLoopTree]) { // block >= this
        val cons = SmtUtils.mkGe(Utils.hashCode(body), Utils.hashCode(loop))
        treeToCons(body) + cons
      } else
        new HashSet[String]
    }

    val thisHashcode = Utils.hashCode(tree)
    tree match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(genEqCons(stmt.getStatements.asScala.toSet + stmt)) {
          (acc, s) => acc ++ treeToCons(s)
        }
      case stmt: DoWhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: EnhancedForLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: WhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: ForLoopTree => // this = init1 = init2 = ...; block >= this
        val initCons = genEqCons(stmt.getInitializer.asScala.toSet + tree)
        val cons = SmtUtils.mkGe(Utils.hashCode(stmt.getStatement), thisHashcode)
        initCons ++ treeToCons(stmt.getStatement) + cons
      case stmt: LabeledStatementTree => // this = body; this = label
        val cons1 = SmtUtils.mkEq(thisHashcode, Utils.hashCode(stmt.getStatement))
        val cons2 = SmtUtils.mkEq(thisHashcode, stmt.getLabel.toString)
        treeToCons(stmt.getStatement) + cons1 + cons2
      case stmt: IfTree => // this = then + else
        val conditions = {
          if (stmt.getElseStatement != null)
            SmtUtils.mkAdd(Utils.hashCode(stmt.getThenStatement), Utils.hashCode(stmt.getElseStatement))
          else
            Utils.hashCode(stmt.getThenStatement)
        }
        val cons = SmtUtils.mkEq(thisHashcode, conditions)
        treeToCons(stmt.getThenStatement) ++ treeToCons(stmt.getElseStatement) + cons
      case stmt: SwitchTree => // this = case1 + case2 + ...
        val cases = {
          val cases = stmt.getCases.asScala
          if (cases.isEmpty) SmtUtils.TRUE
          else if (cases.size == 1) Utils.hashCode(cases.head)
          else SmtUtils.mkAdd(cases.map(casetree => Utils.hashCode(casetree)).toArray: _*)
        }
        val cons = SmtUtils.mkEq(thisHashcode, cases)
        stmt.getCases.asScala.foldLeft(HashSet[String](cons)) {
          (acc, casetree) => acc ++ treeToCons(casetree)
        }
      case stmt: ExpressionStatementTree => new HashSet[String]
      case stmt: ReturnTree => new HashSet[String]
      case stmt: VariableTree => new HashSet[String]
      case stmt: TryTree => // this = try; this = finally; this = catch1 + catch2 + ...
        val cons1 = SmtUtils.mkEq(thisHashcode, Utils.hashCode(stmt.getBlock))
        val cons2 = {
          if (stmt.getFinallyBlock != null) SmtUtils.mkEq(thisHashcode, Utils.hashCode(stmt.getFinallyBlock))
          else SmtUtils.TRUE
        }
        val catches = {
          val catches = stmt.getCatches.asScala
          if (catches.isEmpty) SmtUtils.TRUE
          else if (catches.size == 1) Utils.hashCode(catches.head)
          else SmtUtils.mkAdd(catches.map(catchtree => Utils.hashCode(catchtree)).toArray: _*)
        }
        val cons3 = SmtUtils.mkEq(thisHashcode, catches)
        stmt.getCatches.asScala.foldLeft(HashSet[String](cons1, cons2, cons3)) {
          (acc, catchtree) => acc ++ treeToCons(catchtree)
        } ++ treeToCons(stmt.getBlock) ++ treeToCons(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => treeToCons(stmt.getBlock)
      case _ => new HashSet[String]
    }
  }
}
