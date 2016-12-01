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

abstract class PluginError

case class NoError() extends PluginError

/**
  *
  */
abstract class Plugin() {
    val name : String
    val dependencies : List[String] = List()
    var input: List[TlaSpec] = List()
    var output: List[TlaSpec] = List()
    var throwError : PluginError = NoError()

    def run( newInput: List[TlaSpec] ) : Unit = {
        input = newInput
        output = List()
        throwError = NoError()
        if ( translate() ) {
            PluginController.getNext() match {
                case Some( p ) => p.run( output )
                case _ => return //end
            }
        } else {
            PluginController.getPrevious() match {
                case Some( p ) => p.refine( throwError )
                case _ => return // actual error
            }
        }
    }

    /**
      * Performs processing on the input (plugin-specific reimplement).
      * On success, sets output and returns true.
      * On failure, sets throwError and returns false.
      */
    def translate(): Boolean

    /**
      * Similar to translate, but only called as a response to an error down the chain
      */
    def refine( x : Any ): Boolean
    //def refine( err : PluginError ): Boolean
}

