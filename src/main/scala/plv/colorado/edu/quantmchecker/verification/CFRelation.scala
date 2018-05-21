package plv.colorado.edu.quantmchecker.verification

import com.sun.source.tree._
import net.sf.javailp.Linear

import scala.collection.immutable.HashSet
import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object CFRelation {
  val DEFAULT_LOOP_BOUND = 1000

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
}
