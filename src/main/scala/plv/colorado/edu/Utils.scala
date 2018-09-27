package plv.colorado.edu

import java.io.{File, FileOutputStream, PrintWriter}
import java.nio.file.Paths

import com.sun.source.tree._
import com.sun.source.util.{SourcePositions, Trees}
import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element.{AnnotationMirror, ExecutableElement, TypeElement, VariableElement}
import javax.lang.model.util.{Elements, Types}
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory
import org.checkerframework.javacutil._
import plv.colorado.edu.quantmchecker.qual.Summary
import plv.colorado.edu.quantmchecker.verification.SmtUtils

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
object Utils {
  val NANO = 1000000000
  val DESKTOP_PATH: String = System.getProperty("user.home") + File.separator + "Desktop"
  val LOG_FILE: String = "log.txt"
  new FileOutputStream(new File(Paths.get(DESKTOP_PATH, LOG_FILE).toAbsolutePath.toString)) // Clean up
  val INIT_SUFFIX: String = "_" + SmtUtils.INIT

  val COLLECTION_ADD: HashSet[(String, String)] = HashSet(
    ("java.lang.StringBuilder", "append"),
    ("java.lang.StringBuilder", "insert"),
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

  val ITER_METHOD: HashSet[(String, String)] = HashSet(
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
    ("java.util.regex.Pattern", "matcher"),
    ("java.util.Properties", "keys")
  )

  val ITER_NEXT: HashSet[(String, String)] = HashSet(
    ("java.util.Iterator", "next"),
    ("java.util.regex.Matcher", "find"),
    ("java.util.StringTokenizer", "nextElement"),
    ("java.util.StringTokenizer", "nextToken"),
    ("java.util.Enumeration", "nextElement"),
    ("java.io.BufferedReader", "readLine"),
    ("java.io.InputStreamReader", "read"),
    ("org.htmlparser.lexer.Lexer", "nextNode")
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
      "iterator" -> ITER_METHOD,
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

  def hashCode(o: Object): String = "h" + o.hashCode().toString

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

  def isUnsharingClass(classTree: ClassTree, elements: Elements, trees: Trees): Boolean = {
    val classType = TreeUtils.typeOf(classTree)
    val isAllFldUnsharing = ElementUtils.getAllFieldsIn(TreeUtils.elementFromDeclaration(classTree), elements).asScala.forall { // All fields have to be unsharing
      variableElement =>
        val fldClsTypElement = ElementUtils.enclosingClass(variableElement.getEnclosingElement)
        val fldClsTree = trees.getTree(fldClsTypElement)
        if (fldClsTree != null && fldClsTree.getSimpleName.toString != classTree.getSimpleName.toString) {
          // Don't recursively traverse access paths
          isUnsharingClass(fldClsTree, elements, trees)
        } else true
    }
    val isAllAssignmentUnsharing = ElementUtils.getAllMethodsIn(TreeUtils.elementFromDeclaration(classTree), elements).asScala.forall { // All assignments to class fields should have a new instruction on rhs
      methodElement =>
        val methodTree = trees.getTree(methodElement)
        if (methodTree != null && methodTree.getBody != null) {
          flattenStmt(methodTree.getBody).forall {
            case stmt: ExpressionStatementTree =>
              stmt.getExpression match {
                case assignment: AssignmentTree =>
                  if (TreeUtils.isSelfAccess(assignment.getVariable)) {
                    val rhs = assignment.getExpression
                    rhs.isInstanceOf[NewClassTree] || rhs.isInstanceOf[NewArrayTree]
                  } else true
                case _ => true
              }
            case stmt@_ =>
              if (stmt.toString.contains("table = newTab"))
                println(stmt.getKind)
              true
          }
        } else true
    }
    isAllFldUnsharing && isAllAssignmentUnsharing
  }

  def getReachableCollectionFields(typeElement: TypeElement, elements: Elements, types: Types, accessPaths: HashSet[AccessPath]): HashSet[AccessPath] = {
    ElementUtils.getAllFieldsIn(typeElement, elements).asScala.foldLeft(new HashSet[AccessPath]) {
      (acc, variableElement) =>
        val fldTypMirror = types.erasure(variableElement.asType())
        val fldTypEle: TypeElement = ElementUtils.enclosingClass(variableElement)
        // elements.getTypeElement(fldTypMirror.toString)
        if (fldTypEle != null) {
          val newAccessPathElement = AccessPathElement(variableElement.getSimpleName.toString, fldTypEle)
          val newAccessPaths = accessPaths.foldLeft(new HashSet[AccessPath]) {
            (acc, l) =>
              val noLoop = l.path.forall(e => e.fieldTyp != fldTypEle)
              // Terminate when encountering recursive typed fields
              if (noLoop) acc + AccessPath(newAccessPathElement :: l.path)
              else acc
          }
          // println(newAccessPaths)
          if (Utils.isCollectionTyp(fldTypEle)) {
            acc ++ newAccessPaths
          } else if (getTopPackageName(fldTypEle, types) != getTopPackageName(typeElement, types)) { // Terminate when encountering non user defined classes
            acc
          } else {
            // println(typeElement, fldTypEle.asType().toString, newAccessPathElement)
            if (newAccessPaths.nonEmpty)
              acc ++ getReachableCollectionFields(fldTypEle, elements, types, newAccessPaths)
            else
              acc
          }
        } else acc
    }
  }

  def getReachableCollectionFields(tree: ClassTree, elements: Elements,
                                   types: Types): HashSet[AccessPath] = {
    if (tree == null) return new HashSet[AccessPath]
    val clsTypEle = TreeUtils.elementFromDeclaration(tree)
    val initPath = AccessPath(List(AccessPathElement(tree.getSimpleName.toString, clsTypEle)))
    getReachableCollectionFields(clsTypEle, elements, types, HashSet[AccessPath](initPath))
  }

  def getReachableSize(tree: ClassTree, elements: Elements, types: Types): Int = {
    ???
  }

  def getTopPackageName(typeElement: TypeElement, types: Types): String = {
    val typName = types.erasure(typeElement.asType()).toString.split('.')
    typName.head
  }

  def isCollectionTyp(typeElement: TypeElement): Boolean = {
    Utils.COLLECTION_ADD.exists {
      case (klass, method) => if (klass == typeElement.toString) true else false
    }
  }
}

case class AccessPathElement(fieldName: String, fieldTyp: TypeElement) {
  override def equals(obj: scala.Any): Boolean = {
    obj match {
      case element: AccessPathElement => element.fieldName == fieldName && element.fieldTyp == fieldTyp
      case _ => false
    }
  }

  override def toString: String = fieldName + ": " + fieldTyp.toString
}

case class AccessPath(path: List[AccessPathElement]) {
  override def toString: String = {
    if (path.isEmpty) ""
    else path.foldLeft(path.head.fieldName) { (acc, e) => acc + "." + e.fieldName }
  }
}

case class VarTyp(varElement: VariableElement, anno: String, isInput: Boolean) {
  def getTypMirror(types: Types): TypeMirror = types.erasure(varElement.asType())

  def getTypElement(types: Types): TypeElement = TypesUtils.getTypeElement(getTypMirror(types))

  //elements.getTypeElement(getTypMirror(types).toString)
}