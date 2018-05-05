package plv.colorado.edu

import java.io.{File, FileOutputStream, PrintWriter}
import java.nio.file.Paths
import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element.{AnnotationMirror, ExecutableElement}

import com.sun.source.tree.{CompilationUnitTree, Tree}
import com.sun.source.util.SourcePositions
import org.checkerframework.javacutil.AnnotationUtils

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object Utils {
  private val DESKTOP_PATH = System.getProperty("user.home") + File.separator + "Desktop"
  private val LOG_FILE = "log.txt"
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
    ("java.util.Hashtable", "add"),
    ("java.util.ByteBuffer", "put")
  )

  val DEC_REMAINDER: HashSet[(String, String)] = HashSet(
    ("java.io.BufferedReader", "readline")
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

  /**
    *
    * @param klass receiver type of the method invocation site
    * @param method method invocation
    * @return if the invocation is a collection add
    */
  def isCollectionAdd(klass: TypeMirror, method: ExecutableElement): Boolean = {
    val className = klass.toString
    val methodName = method.getSimpleName.toString
    COLLECTION_ADD.contains((className, methodName))
  }

  def logging(msg: String): Unit ={
    val logger = new PrintWriter(new FileOutputStream(new File(Paths.get(DESKTOP_PATH, LOG_FILE).toAbsolutePath.toString), true))
    logger.println(msg)
    logger.close()
  }
}
