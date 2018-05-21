package plv.colorado.edu.quantmchecker.verification

import com.sun.source.tree.MethodTree
import net.sf.javailp._

import scala.collection.immutable.HashSet
import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object SolveLP {
  def solveLp[T](constraints: Iterable[LpCons],
                 obj: Option[Linear],
                 // vars: Iterable[String],
                 // varType: Class[T] = classOf[Integer].asInstanceOf,
                 lowerBound: Number = 0,
                 optType: OptType = OptType.MAX): Option[Result] = {
    val DEBUG = false
    obj match {
      case Some(obj) =>
        val factory = new SolverFactoryLpSolve()
        factory.setParameter(Solver.VERBOSE, 0)
        // set timeout to 100 seconds
        factory.setParameter(Solver.TIMEOUT, 100)
        val problem = new Problem()
        constraints.foreach(c => problem.add(c.cons, c.op, c.rhs))
        problem.setObjective(obj, optType)
        val vars = constraints.foldLeft(new HashSet[String]) {
          (acc, c) => acc ++ LpCons.getVars(c)
        }
        vars.foreach(v => problem.setVarType(v, classOf[Integer]))
        vars.foreach(v => problem.setVarLowerBound(v, lowerBound))
        if (DEBUG) println(problem)
        Option(factory.get.solve(problem))
      case None => if (DEBUG) println("Empty obj"); None
    }
  }

  /**
    *
    * @param methodTree a method
    * @param obj        an optimization object
    * @return max value of the object under the constraints generated from the method
    */
  def optimizeWithinMethod(methodTree: MethodTree, obj: Linear): Option[Result] = {
    val cons1 = CFRelation.treeToCons(methodTree.getBody)
    val cons2 = new Linear // body = 1
    if (methodTree.getBody != null)
      cons2.add(1, methodTree.getBody.hashCode().toString)

    val cons: Set[LpCons] = cons1.map(l => LpCons(l, "=", 0)) + LpCons(cons2, "=", 1)

    val vars = cons.foldLeft(new HashSet[String]) {
      (acc, c) => acc ++ LpCons.getVars(c)
    }

    val ifEveryObjVarIsConstrained = obj.getVariables.asScala.forall(v => vars.contains(v.toString))
    if (ifEveryObjVarIsConstrained)
      solveLp(cons, Some(obj))
    else
      None
  }
}
