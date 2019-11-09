package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.impl.Lift
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import javax.inject.{Inject, Singleton}

import scala.collection.immutable.HashMap

// Igor @ 07.11.2019: refactoring needed
// TODO: move object after class
// TODO: move private methods after the public methods
// TODO: add comments

object IncrementalRenaming {
  private val separator : String = "$"
  private val separatorRegex = s"[$separator]"

  /**
    * makeName( x, i ) constructs the representation of x_i, as recognized by the renaming methods.
    */
  def makeName( base: String, ctr: Int ) : String = s"$base$separator$ctr"

  type counterMapType = Map[String,Int]

  /**
    * Attempts to read a variable name as a (base,counter) pair. Reading a variable that's not written
    * in the renaming-representation returns None, otherwise this method has the following property:
    * parseName( makeName( a, b ) ) = Some( (a,b) )
    */
  def parseName( name : String ) : Option[(String, Int)] = {
    name.split( separatorRegex ) match {
      // Already renamed before
      case Array( n, i ) if i forall {_.isDigit} => Some((n, i.toInt))
      // Never renamed before
      case Array( n ) => None
      // Error
      case _ => throw new IllegalArgumentException("Variable names should never contain more than one separator")
    }
  }

  /** Attempts to read the base-name of a variable. Has the following property:
    * getBase( makeName( a, b ) ) = a
    */
  def getBase( name : String ) : String = parseName( name ).map( _._1 ).getOrElse( name )

  /**
    * Merges two maps of type `counterMapType`. The new map has the following properties:
    *   1) \A k \in m1.keys \ m2.keys . mergeNameCounters( b )( m1, m2 )[k] = m1[k]
    *   2) \A k \in m2.keys \ m1.keys . mergeNameCounters( b )( m1, m2 )[k] = m2[k]
    *   3) \A k \in m1.keys \cap m2.keys .
    *       mergeNameCounters( b )( m1, m2 )[k] = IF b THEN max(m1[k],m2[k]) ELSE min(m1[k],m2[k])
    */
  def mergeNameCounters( takeMax: Boolean )( m1 : counterMapType, m2 : counterMapType ) : counterMapType = {
    val selectorFun : (Int, Int) => Int = if (takeMax) math.max else math.min
    m2.foldLeft( m1 ) { case (m, (k, v)) =>
      m + ( k -> selectorFun( m1.getOrElse( k, v ), v ) )
    }
  }

  /**
    * Computes a map of type `counterMapType`, that maps each base name n to the largest,
    * if `takeMax` = true, or the smallest, if `takeMax` = false, counter k,
    * for which a NameEx( makeName( n, k ) ) appears in a subexpression of `ex`.
    */
  def nameCounterMapFromEx( takeMax: Boolean )( ex: TlaEx ) : counterMapType = ex match {
    case NameEx( n ) => parseName( n ) match {
      case Some((base, ctr)) => Map( base -> ctr )
      case None => Map.empty // No need to store n -> 0
    }

    case OperEx( _, args@_* ) =>
      args.map( nameCounterMapFromEx( takeMax) ).foldLeft(Map.empty[String,Int]){ mergeNameCounters( takeMax ) }

    case LetInEx( body, defs@_* ) =>
      defs.map( nameCounterMapFromDecl( takeMax ) ).foldLeft( nameCounterMapFromEx( takeMax )( body ) ) {
        mergeNameCounters( takeMax )
      }

    case _ => Map.empty
  }

  /**
    * For a given TlaOperDecl d, computes nameCounterMapFromEx( d.body ), extended with entries for
    * the formal parmeters and the name of d.
    */
  def nameCounterMapFromDecl( takeMax: Boolean )( decl : TlaDecl ) : counterMapType = decl match {
    case TlaOperDecl( name, params, body ) =>
      val nameAndParamMap = ( parseName( name ) ++: params.flatMap( p => parseName( p.name ) ) ).toMap
      val bodyMap = nameCounterMapFromEx( takeMax )( body )
      mergeNameCounters( takeMax )( bodyMap, nameAndParamMap )
    case _ => Map.empty
  }

  /**
    * Computes then merges maps for all declarations.
    */
  def nameCounterMapFromDecls( takeMax: Boolean )( decls: Traversable[TlaDecl] ) : counterMapType =
    decls.map( nameCounterMapFromDecl( takeMax ) ).foldLeft( Map.empty[String, Int] ) { mergeNameCounters( takeMax ) }

  /**
    * If `name` is of the form makeName( a, b ) and offsets contains a,
    * returns makeName( a, b - offsets[a] ), otherwise returns `name`.
    * Throws if b - offsets[a] <= 0.
    */
  def offsetName( offsets : counterMapType )( name : String ) : String = parseName( name ) match {
    case Some( (base, ctr) ) =>
      offsets.getOrElse( base, 0 ) match {
        case 0 => name
        case j =>
          val newCtr = ctr - j
          assert( newCtr > 0 )
          makeName( base, newCtr )
      }
    case None => name
  }
}

/**
  * Unlike Renaming, IncrementalRenaming is intended to maintain concise names under arbitrary re-application
  */
@Singleton
class IncrementalRenaming @Inject()(tracker : TransformationTracker) extends TlaExTransformation {

  import IncrementalRenaming._

  private var nameCounters : Map[String, Int] = HashMap.empty[String, Int]

  /**
    * Incrementally rename all declarations in a module, so every variable is declared only once.
    */
  def renameInModule: TlaModuleTransformation = {
    mod => new TlaModule(mod.name, syncAndNormalizeDs(mod.declarations).toSeq)
  }

  /**
    * Generates the next unique name with the given base.
    */
  private def getNextUnique( base : String ) : String = {
    val newCtr = 1 + nameCounters.getOrElse( base, 0 )
    nameCounters += base -> newCtr

    makeName( base, newCtr )
  }

  /**
    * Safety wrapper, ensures getNextUnique is always called with the base name
    */
  private def getNextUniqueFromBase( name: String ) = getNextUnique( getBase( name ) )

  /**
    * Returns y, but establishes tracking between x and y. Needed for better granularity of tracking.
    */
  private def trackedSubstitution( x : TlaEx, y : TlaEx ) = tracker.track( _ => y )( x )

  private def rename( alreadyRenamed: Map[String,String] ): TlaExTransformation = tracker.track {
    case ex @ NameEx(name) =>
      // If a name has been marked for replacement (i.e. is an entry in alreadyRenamed)
      // we simply substitute in the pre-computed new name
      if ( alreadyRenamed.contains( name ) )
        trackedSubstitution( ex, NameEx( alreadyRenamed( name ) ) )
      else
        ex

    // Certain operators introduce new bound variables
    case OperEx(op, nex@NameEx(name), otherArgs@_*)
      if op == TlaSetOper.filter
        || op == TlaBoolOper.exists || op == TlaBoolOper.forall
        || op == TlaOper.chooseBounded || op == TlaOper.chooseUnbounded
        || op == TlaOper.chooseIdiom =>
      // We compute a unique name for the given base and store it in alreadyRenamed.
      // Recursive calls to subexpressions will take care of all the replacements,
      // where the bound variable appears
      val newName = getNextUniqueFromBase( name )
      val newRenamed = alreadyRenamed + ( name -> newName )
      val newArgs = otherArgs.map( rename( newRenamed ) )
      OperEx( op, trackedSubstitution( nex, NameEx( newName ) ) +: newArgs : _* )

    // Certain operators introduce several bound variables at once
    case OperEx( op, result, varsAndSets@_* )
      if op == TlaSetOper.map || op == TlaFunOper.funDef =>

      // From the syntax we know that evey even-indexed subexpression is a variable name
      val names = varsAndSets.zipWithIndex.collect { case (e : NameEx, i) if i % 2 == 0 => e }

      // Sanity check
      assert( 2 * names.length == varsAndSets.length )

      // Just as in the single-variable case, we assign a new name for each bound variable
      val newRenamed = names.map( _.name ).foldLeft( alreadyRenamed ) { case (m, n) =>
        m + ( n -> getNextUniqueFromBase( n ) )
      }

      // And recurse
      val newArgs = ( result +: varsAndSets ).map {
        rename( newRenamed )
      }

      OperEx(op, newArgs: _*)

    // All other operators don't introduce any variables, so we just recurse
    case ex@OperEx(op, args@_*) =>
      val newArgs = args.map( rename( alreadyRenamed ) )
      if ( args == newArgs ) ex
      else OperEx( op, newArgs : _* )

    // LET-IN operators introduce operator names (and potentially parameter names), which
    // we rename the same way as bound variables
    case LetInEx( body, defs@_* ) =>
      val opersAndFParamsNameMap = ( defs flatMap {
        // For each operator the name and all parameters are assigned new names
        case TlaOperDecl( n, params, _ ) => ( n -> getNextUniqueFromBase( n ) ) +: (
          params map { p =>
            val pName = p.name
            pName -> getNextUniqueFromBase( pName )
          } )
      } ).toMap

      val newRenamed = alreadyRenamed ++ opersAndFParamsNameMap

      val newRenaming = rename( newRenamed )

      // Having computed the new names, we have to change the declarations and use the precomputed new names
      val newDefs = defs map {
        case TlaOperDecl( n, ps, b ) =>
          TlaOperDecl(
            opersAndFParamsNameMap( n ),
            ps map {
              case SimpleFormalParam( p ) => SimpleFormalParam( opersAndFParamsNameMap( p ) )
              case OperFormalParam( p, a ) => OperFormalParam( opersAndFParamsNameMap( p ), a )
            },
            // We recurse over operator bodies, because newRenamed contains parameter
            // and operator renamings
            newRenaming( b )
          )
      }
      // Finally, we recurse on the body
      val newBody = newRenaming( body )
      LetInEx( newBody, newDefs : _* )

    // If it's not an operator, a let-in or a name we do nothing
    case ex => ex
  }

  /**
    * Calls rename, with the initial renaming map (= empty)
    */
  override def apply( ex : TlaEx ) : TlaEx = rename( alreadyRenamed = Map.empty )( ex )
  def applyToDecl : TlaDecl => TlaDecl = Lift.exToDecl( apply )
  def applyToDecls : Traversable[TlaDecl] => Traversable[TlaDecl] = Lift.declToDecls( applyToDecl )

  /**
    * Reduces all variable counters by the amount specified in offsets.
    */
  private[lir] def shiftCounters( offsets: counterMapType ): TlaExTransformation = tracker.track {
    case ex @ NameEx(name) =>
      val newName = offsetName( offsets )( name )
      if ( newName == name ) ex
      else NameEx( newName )

    case ex@OperEx(op, args@_*) =>
      val newArgs = args.map( shiftCounters( offsets ) )
      if ( args == newArgs ) ex
      else OperEx( op, newArgs : _* )

    case ex@LetInEx( body, defs@_* ) =>
      val offsetFn : String => String = offsetName( offsets )
      val self = shiftCounters( offsets )
      val newDefs = defs map {
        case TlaOperDecl( n, params, b ) =>
          TlaOperDecl(
            offsetFn( n ),
            params map {
              case SimpleFormalParam( p ) => SimpleFormalParam( offsetFn( p ) )
              case OperFormalParam( p, a ) => OperFormalParam( offsetFn( p ), a )
            },
            self( b )
          )
      }

      val newBody = self( body )
      if ( newBody == body && newDefs == defs ) ex
      else LetInEx( newBody, newDefs : _* )

    case ex => ex
  }

  // Lifted to decl
  private def shiftCountersD( offsets : counterMapType ) : TlaDecl => TlaDecl =
    Lift.exToDecl( shiftCounters( offsets ) )

  // lifted to decls
  private def shiftCountersDs( offsets : counterMapType ) : Traversable[TlaDecl] => Traversable[TlaDecl] =
    Lift.declToDecls( shiftCountersD( offsets ) )

  /**
    * This method "normalizes" a previously renamed expression, so that the variable counter for each variable
    * starts at 1, if only variables appearing in `ex` are considered
    * E.g. x5 + y3 > z4 becomes x1 + y1 > z1
    * Importatntly, it is assumed that `ex` has been renamed at least once.
    */
  def normalize( ex: TlaEx ) : TlaEx = {
    val offsetMap = nameCounterMapFromEx( takeMax = false )( ex ) withFilter { _._2 > 1 } map {
      case (k,v) => (k, v - 1 )
    }
    shiftCounters( offsetMap )( ex )
  }

  def normalizeExs( exs: Traversable[TlaEx] ) : Traversable[TlaEx] = {
    val offsetMap = exs.map(
      nameCounterMapFromEx( takeMax = false )
    ).foldLeft(Map.empty[String, Int]) {
      mergeNameCounters( takeMax = false )
    } withFilter { _._2 > 1 } map {
      case (k,v) => (k, v - 1 )
    }

    exs map { shiftCounters(offsetMap) }
  }

  // Lifted to decl
  def normalizeD : TlaDecl => TlaDecl =
    Lift.exToDecl( normalize )

  // lifted to decls
  def normalizeDs( decls : Traversable[TlaDecl] ) : Traversable[TlaDecl] = {
    val offsetMap = nameCounterMapFromDecls( takeMax = false )( decls ) withFilter { _._2 > 1 } map {
      case (k,v) => (k, v - 1 )
    }
    shiftCountersDs( offsetMap )( decls )
  }

  /**
    * Updates `nameCounters`, so that every for every entry a -> b, if makeName(a, c) appears in
    * `ex`, it holds that c <= b
    */
  def syncFrom( ex: TlaEx ): Unit = {
    val maxMap = nameCounterMapFromEx( takeMax = true )( ex )
    nameCounters = mergeNameCounters( takeMax = true )( nameCounters, maxMap )
  }

  // Lifted to decl
  private def syncFromD : TlaDecl => Unit = {
    case TlaOperDecl( _, _, b ) => syncFrom( b )
    case _ => ()
  }

  // Lifted to decls
  private def syncFromDs : Traversable[TlaDecl] => Unit = _ foreach syncFromD

  /**
    * Performs the following steps, in order:
    *   - Syncs from ex
    *   - Renames ex to ex'
    *   - Normalizes ex'
    */
  def syncAndNormalize( ex: TlaEx ) : TlaEx = {
    syncFrom( ex )
    normalize( apply( ex ) )
  }

  def syncAndNormalizeExs( exs: Traversable[TlaEx] ) : Traversable[TlaEx] = {
    exs foreach syncFrom
    normalizeExs( exs map { apply } )
  }

  // Lifted to decl
  def syncAndNormalizeD( d: TlaDecl) : TlaDecl = {
    syncFromD( d )
    normalizeD( applyToDecl( d ) )
  }

  // Lifted to decls
  def syncAndNormalizeDs( ds: Traversable[TlaDecl]) : Traversable[TlaDecl] = {
    syncFromDs( ds )
    normalizeDs( applyToDecls( ds ) )
  }

}
