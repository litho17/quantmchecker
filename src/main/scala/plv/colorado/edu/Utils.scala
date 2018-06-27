package plv.colorado.edu

import java.io.{File, FileOutputStream, PrintWriter}
import java.nio.file.Paths
import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element.{AnnotationMirror, ExecutableElement}

import com.sun.source.tree._
import com.sun.source.util.SourcePositions
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TypeAnnotationUtils}
import plv.colorado.edu.quantmchecker.qual.Summary

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
object Utils {
  val DESKTOP_PATH: String = System.getProperty("user.home") + File.separator + "Desktop"
  val LOG_FILE: String = "log.txt"
  new FileOutputStream(new File(Paths.get(DESKTOP_PATH, LOG_FILE).toAbsolutePath.toString)) // Clean up

  val COLLECTION_ADD: HashSet[(String, String)] = HashSet(
    ("java.lang.StringBuilder", "append"),
    ("java.lang.StringBuffer", "append"),
    ("java.util.ArrayList", "add"),
    ("java.util.List", "add"),
    ("java.util.LinkedList", "add"),
    ("java.util.AbstractList", "add"),
    ("java.util.Set", "add"),
    ("java.util.HashSet", "add"),
    ("java.util.EnumSet", "add"),
    ("java.util.TreeSet", "add"),
    ("java.util.Map", "put"),
    ("java.util.HashMap", "put"),
    ("java.util.EnumMap", "put"),
    ("java.util.ConcurrentHashMap", "put"),
    ("java.util.AbstractMap", "put"),
    ("java.util.TreeMap", "put"),
    ("java.util.LinkedHashMap", "put"),
    ("java.util.IdentityHashMap", "put"),
    ("java.util.Collection", "add"),
    ("java.util.Queue", "add"),
    ("java.util.Queue", "offer"),
    ("java.util.PriorityQueue", "add"),
    ("java.util.PriorityQueue", "offer"),
    ("java.util.Deque", "add"),
    ("java.util.Deque", "offer"),
    ("java.util.Stack", "push"),
    ("java.util.Vector", "add"),
    ("java.util.Vector", "addElement"),
    ("java.util.Hashtable", "add"),
    ("java.util.ByteBuffer", "put")
  )

  val COLLECTION_REMOVE: HashSet[(String, String)] = HashSet(
    ("java.lang.ArrayList", "remove"),
    ("java.util.List", "remove"),
    ("java.util.LinkedList", "remove"),
    ("java.util.AbstractList", "remove"),
    ("java.util.Set", "remove"),
    ("java.util.HashSet", "remove"),
    ("java.util.EnumSet", "remove"),
    ("java.util.TreeSet", "remove"),
    ("java.util.Map", "remove"),
    ("java.util.HashMap", "remove"),
    ("java.util.EnumMap", "remove"),
    ("java.util.ConcurrentHashMap", "remove"),
    ("java.util.AbstractMap", "remove"),
    ("java.util.TreeMap", "remove"),
    ("java.util.LinkedHashMap", "remove"),
    ("java.util.IdentityHashMap", "remove"),
    ("java.util.Collection", "remove"),
    ("java.util.Queue", "remove"),
    ("java.util.Queue", "poll"),
    ("java.util.PriorityQueue", "remove"),
    ("java.util.PriorityQueue", "poll"),
    ("java.util.Deque", "remove"),
    ("java.util.Deque", "poll"),
    ("java.util.Stack", "pop"),
    ("java.util.Vector", "remove"),
    ("java.util.Hashtable", "remove")
  )

  val ITER: HashSet[(String, String)] = HashSet(
    ("java.lang.ArrayList", "iterator"),
    ("java.util.List", "iterator"),
    ("java.util.LinkedList", "iterator"),
    ("java.util.AbstractList", "iterator"),
    ("java.util.Set", "iterator"),
    ("java.util.HashSet", "iterator"),
    ("java.util.EnumSet", "iterator"),
    ("java.util.TreeSet", "iterator"),
    ("java.util.Map", "iterator"),
    ("java.util.HashMap", "iterator"),
    ("java.util.EnumMap", "iterator"),
    ("java.util.ConcurrentHashMap", "iterator"),
    ("java.util.AbstractMap", "iterator"),
    ("java.util.TreeMap", "iterator"),
    ("java.util.LinkedHashMap", "iterator"),
    ("java.util.IdentityHashMap", "iterator"),
    ("java.util.Collection", "iterator"),
    ("java.util.Queue", "iterator"),
    ("java.util.Queue", "iterator"),
    ("java.util.PriorityQueue", "iterator"),
    ("java.util.PriorityQueue", "iterator"),
    ("java.util.Deque", "iterator"),
    ("java.util.Deque", "iterator"),
    ("java.util.Stack", "iterator"),
    ("java.util.Vector", "iterator"),
    ("java.util.Hashtable", "iterator"),
    ("java.util.regex.Pattern", "matcher")
  )

  val ITER_NEXT: HashSet[(String, String)] = HashSet(
    ("java.util.Iterator", "next"),
    ("java.util.regex.Matcher", "find"),
    ("java.util.StringTokenizer", "nextElement"),
    ("java.util.StringTokenizer", "nextToken"),
    ("java.util.Enumeration", "nextElement"),
    ("java.io.BufferedReader", "readLine"),
    ("java.io.InputStreamReader", "read")
    // ("java.util.Queue", "poll")
  )

  /**
    *
    * @param anno annotation
    * @return the value stored in string array (as type arguments)
    */
  def extractArrayValues(anno: AnnotationMirror, valueName: String): List[String] = {
    val valMap = anno.getElementValues
    if (valMap.isEmpty)
      List()
    else
      AnnotationUtils.getElementValueArray(anno, valueName, classOf[String], true).asScala.toList
  }

  def extractValue(anno: AnnotationMirror, valueName: String): String = {
    val valMap = anno.getElementValues
    if (valMap.isEmpty)
      ""
    else
      AnnotationUtils.getElementValue(anno, valueName, classOf[String], true)
  }

  def getLineNumber(node: Tree, positions: SourcePositions, root: CompilationUnitTree): Long = {
    root.getLineMap.getLineNumber(positions.getStartPosition(root, node))
  }

  def getMethodSummary(method: ExecutableElement, atypeFactory: BaseAnnotatedTypeFactory): Option[String] = {
    if (method == null) return None
    val elements = atypeFactory.getElementUtils
    val SUMMARY: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Summary])

    val summaries = atypeFactory.getDeclAnnotations(method).asScala.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, SUMMARY)).toList
    if (summaries.size == 1) Option(Utils.extractArrayValues(summaries.head, "value").head) else None
  }

  /**
    *
    * @param query        a collection operation
    * @param klass        class that declares the method
    * @param method       the method
    * @param atypeFactory type factory
    * @return if the method is indeed the query
    */
  def isColWhat(query: String,
                klass: TypeMirror,
                method: ExecutableElement,
                atypeFactory: BaseAnnotatedTypeFactory): Boolean = {
    val map = HashMap[String, HashSet[(String, String)]](
      "add" -> COLLECTION_ADD,
      "remove" -> COLLECTION_REMOVE,
      "iterator" -> ITER,
      "next" -> ITER_NEXT
    )

    val className = if (klass == null) "" else TypeAnnotationUtils.unannotatedType(klass).toString
    val methodName = if (method == null) "" else method.getSimpleName.toString
    map.get(query) match {
      case Some(collection) =>
        if (collection.contains((className, methodName))) true else {
          getMethodSummary(method, atypeFactory) match {
            case Some(summary) => query.equalsIgnoreCase(summary)
            case None => false
          }
        }
      case None => false
    }
  }

  /**
    *
    * @param msg a message
    *            write a message into the logging file
    */
  def logging(msg: String): Unit = {
    val logger = new PrintWriter(new FileOutputStream(new File(Paths.get(DESKTOP_PATH, LOG_FILE).toAbsolutePath.toString), true))
    logger.println(msg)
    logger.close()
  }

  def hashCode(tree: Object): String = "h" + tree.hashCode().toString

  def isValidId(str: String): Boolean = {
    val pattern = "(?:\\b[_a-zA-Z]|\\B\\$)[_$a-zA-Z0-9]*+"
    str.matches(pattern)
  }

  /**
    *
    * @param node a statement tree
    * @return collect a set of all leave statements
    *         Note: All other StatementTrees are ignored
    */
  def flattenStmt(node: StatementTree): HashSet[StatementTree] = {
    node match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(new HashSet[StatementTree])((acc, s) => acc ++ flattenStmt(s))
      case stmt: DoWhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: EnhancedForLoopTree => flattenStmt(stmt.getStatement)
      case stmt: ForLoopTree =>
        stmt.getInitializer.asScala.foldLeft(flattenStmt(stmt.getStatement)) {
          (acc, s) => acc ++ flattenStmt(s)
        }
      case stmt: WhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: LabeledStatementTree => flattenStmt(stmt.getStatement)
      case stmt: IfTree => flattenStmt(stmt.getThenStatement) ++ flattenStmt(stmt.getElseStatement)
      case stmt: SwitchTree =>
        stmt.getCases.asScala.foldLeft(new HashSet[StatementTree]) {
          (acc, caseTree) => caseTree.getStatements.asScala.foldLeft(acc)((acc2, s) => acc2 ++ flattenStmt(s))
        }
      case stmt: ExpressionStatementTree => HashSet[StatementTree](stmt)
      case stmt: ReturnTree => HashSet[StatementTree](stmt)
      case stmt: VariableTree => HashSet[StatementTree](stmt)
      case stmt: TryTree => flattenStmt(stmt.getBlock) ++ flattenStmt(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => flattenStmt(stmt.getBlock)
      case _ => new HashSet[StatementTree]
    }
  }
}
