package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap

/**
  * When computing operator types using the template-based approach,
  * constructing templates for each individual operator in a specification is slow
  * and expensive, since several constraints are encoded multiple times.
  *
  * Consider the example:
  * A == ...
  * B == ... A() ...
  * C == ... B() ...
  *
  * If we construct the templates of all operators, we will actually create constraints on the
  * type of A three times and constraints on the type of B twice, since the template
  * for B is invoked when creating the constraints for C, and so on.
  *
  * The solution to this is to compute the dependency graph (forest, in the absence of recursion)
  * of all operators in a given specification and construct templates only for "roots",
  * which are either operators with no dependencies (basic roots),
  * or arbitrary operators in a mutual-recursion dependency cycle (non-basic roots).
  */
object DependencyGraph {

  abstract class Node {
    val isRecursive : Boolean
    val children    : Set[String]
  }

  sealed case class RootNode( children : Set[String] ) extends Node {
    val isRecursive : Boolean = false
  }

  sealed case class InternalNode(
                                  opName : String,
                                  isRecursive : Boolean,
                                  children : Set[String]
                                ) extends Node

  type NodeMap = Map[String, InternalNode]

  def construct( bodyMap : BodyMap ) : DependencyGraph = {
    var constructed = Map.empty[String, InternalNode]
    var explorationStack = Vector.empty[String]
    var knownRecursive = Set.empty[String]
    var notBasicRoots = Set.empty[String]

    def processOper( name : String ) : Unit = {
      // If we've already constructed the node, skip
      if ( !constructed.contains( name ) ) {
        // If not, check whether the current operator is recursive.
        // If it is, it must be in the exploration stack (in the general case
        // of mutual recursion).
        explorationStack.indexOf( name ) match {
          case -1 => // Not recursive
            explorationStack = name +: explorationStack
            // We fetch the body ...
            bodyMap.get( name ) match {
              case Some( TlaOperDecl( _, _, body ) ) =>
                // ... and scan it for any operator calls
                val children = subCalls( body )
                // Any operator that is called in such a way, cannot be a basic root,
                // (though it may possibly be chosen as a non-basic root, in the mutual recursion setting)
                notBasicRoots ++= children
                // We recursively explore dependencies of the child-nodes-to-be (DFS)
                children foreach processOper
                // If there was re-entry, this operator name was added to the knownRecursive collection
                val isRecursive = knownRecursive.contains( name )
                // We construct its node and pop the stack
                val node = InternalNode( name, isRecursive, children )
                constructed += name -> node
                explorationStack = explorationStack.tail
              case None =>
                throw new IllegalArgumentException( s"The body of operator $name is unknown" )
            }
          case n =>
            // All of the operators in the stack above the first appearance
            // are (mutually) recursive
            knownRecursive ++= explorationStack.take( n + 1 )
        }
      }
    }

    // We construct all the nodes
    val allOpers = bodyMap.keySet
    allOpers foreach processOper

    // All that remains is to determine the roots.
    // We take as basic roots all the operators which were
    // /not added to the `notBasicRoots` set (i.e. not called ba another operator)
    val basicRoots = allOpers -- notBasicRoots

    // We now remove all the connected components rooted at basic roots from consideration
    val getCC : String => Set[String] = getConnectedComponent( _, constructed )
    val covered = basicRoots flatMap getCC
    val remaining = allOpers -- covered

    // Finally, we iteratively pick an arbitrary operator as a nonbasic root and remove
    // its connected component from consideration
    def pickLoopRoots( ccs : Set[String] ) : Set[String] =
      if ( ccs.isEmpty ) Set.empty
      else {
        val someElem = ccs.head
        pickLoopRoots( ccs -- getCC( someElem ) ) + someElem
      }

    val loopRoots = pickLoopRoots( remaining )

    // The final set of roots consists of all the basic roots and the selected loop roots
    new DependencyGraph {
      val root    : RootNode = RootNode( basicRoots ++ loopRoots )
      val nodeMap : NodeMap  = constructed
    }
  }

  private def getConnectedComponent( name : String, nodeMap : NodeMap ) : Set[String] = {
    def getInternal( name : String, seen : Set[String] ) : Set[String] =
      nodeMap( name ) match {
        case InternalNode( _, _, children ) =>
          val newSeen = seen + name
          ( ( children -- newSeen ) flatMap {
            getInternal( _, newSeen )
          } ) + name
      }

    getInternal( name, Set.empty )
  }

  private def subCalls( ex : TlaEx ) : Set[String] = ex match {
    case OperEx( TlaOper.apply, NameEx( otherName ), args@_* ) =>
      ( args map subCalls ).foldLeft( Set( otherName ) ) {
        _ ++ _
      }
    // We explicitly disregard dependencies on
    // operators used as type annotations, because they are
    // ignored in template generation. This method forces them to become roots
    case OperEx( BmcOper.withType, expr, annot ) =>
      subCalls(expr)
    // Similar for UNCHANGED
    case OperEx( TlaActionOper.unchanged, _ ) =>
      Set.empty[String]
    case OperEx( _, args@_* ) =>
      ( args map subCalls ).foldLeft( Set.empty[String] ) {
        _ ++ _
      }
    case LetInEx( letInBody, defs@_* ) =>
      ( defs map { case TlaOperDecl( _, _, b ) => subCalls( b ) } ).foldLeft(
        subCalls( letInBody )
      ) {
        _ ++ _
      } -- ( defs map {
        _.name
      } )
    case _ => Set.empty[String]
  }

}

abstract class DependencyGraph {

  import DependencyGraph._

  val root    : RootNode
  val nodeMap : Map[String, InternalNode]
}
