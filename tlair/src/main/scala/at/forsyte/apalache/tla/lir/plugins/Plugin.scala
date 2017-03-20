package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir.TlaSpec
import collection.mutable.HashMap

class PluginTree

/**
  * There can only ever be one controller, a singleton object.
  * A controller creates a plugin tree from dependency information and consumes them in BFS order. (Independent chains
  * may be executed in parallel)
  */
object PluginController {
  //val allocator : IDAllocator[String] = new IDAllocator[String]();
  var plugins: PluginTree = new PluginTree()
  val maxParallel: Int = 1

  /**
    * Creates a plugin graph carrying dependency information. If plugin p1 depends on p2 then there must exist a path
    * from p2 to p1. If a cycle is found in the graph, the process must fail (circular dependency).
    * This guarantees a DAG upon successful execution.
    *
    * @param plugins - The plugins, in arbitrary order.
    */
  def makePluginTree( plugins: List[ Plugin ] ): Unit = {
    // Allocate all plugins, later use only IDs
    //plugins.foreach( (p : Plugin ) => allocator.allocate( p.name ) )

    val depMap : HashMap[String, String] = HashMap()
    plugins.foreach(
      (p : Plugin ) =>  p.dependencies.foreach(
        ( pluginName : String ) => depMap.put( p.name, pluginName )
      )
    )

  }

  /**
    * Sets the input ot all top level (fully independent) plugins. A plugin is considered fully independent if it has
    * no dependencies on any other plugins.
    *
    * @param tlaSpec The initial input of all fully independent plugins.
    */
  def prepareInput( tlaSpec: TlaSpec ): Unit = {} // TODO

  def getNext( ) : Option[Plugin] = { // TODO
    None
  }

  def getPrevious( ) : Option[Plugin] = { // TODO
    None
  }

}

abstract class PluginError extends Exception

case class NoError() extends PluginError
case class ActualError() extends PluginError


/**
  *
  */
abstract class Plugin() {
  val name : String
  /** Database dependencies */
  val dependencies : List[String]
  var input: TlaSpec = null
  var output: TlaSpec = null
  var throwError : PluginError = NoError()

  private def pushForward(): Unit ={
    PluginController.getNext() match {
      case Some( p ) => p.run( output )
      case _ => return // end
    }
  }

  def run( newInput: TlaSpec ) : Unit = {
    input = newInput
    output = null
    throwError = NoError( )
    translate( )
  }

  /**
    * Performs processing on the input (plugin-specific reimplement).
    * On failure, sets throwError.
    */
  protected def translate() : Unit

  /**
    * Similar to run, but only called as a response to an error down the chain
    */
  def refine( err : PluginError ): Unit = {
    output = null
    throwError = NoError( )
    reTranslate( err: PluginError )
  }

  /**
    * Performs alternative processing on the input, responding to some PluginError down the chain (plugin-specific reimplement).
    * On failure, sets throwError.
    */
  protected def reTranslate( err: PluginError ): Unit

}

