package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.src.SourceLocation
import at.forsyte.apalache.tla.lir.storage.SourceLocator

class TransitionOrder( sourceLocator : SourceLocator ) {

  private type orderTup = (String, Int, Int)

  private def tupProjection( s : SourceLocation ) : orderTup =
    (s.filename, s.region.start.line, s.region.start.column)

  /**
    * a < b iff
    *
    * (a.filename, a.region.start.line, a.region.start.column)
    * <
    * (b.filename, b.region.start.line, b.region.start.column)
    */
  private def locCmp( a : SourceLocation, b : SourceLocation ) : Int =
    Ordering[orderTup].compare( tupProjection( a ), tupProjection( b ) )

  private def locLT( a: SourceLocation, b: SourceLocation ): Boolean =
    Ordering[orderTup].lt( tupProjection( a ), tupProjection( b ) )


  private def dropPrefixZeros( s : Seq[Int] ) : Int = s match {
    case Nil => 0
    case v +: Nil => v
    case v +: vs =>
      if ( v != 0 )
        v
      else
        dropPrefixZeros( vs )
  }

  private def lexCmpSeqs[T]( cmpFun : (T, T) => Int )( a : Seq[T], b : Seq[T] ) : Int =
    dropPrefixZeros(
      a.zip( b ) map { case (x, y) => cmpFun( x, y ) }
    )

  /**
    * we assume |a| = |b|, as is the case when a and b are assignment selections
    */
  private def seqLocLT( a : Seq[SourceLocation], b : Seq[SourceLocation] ) : Boolean =
    lexCmpSeqs( locCmp )( a, b ) < 0

  private def getSortedLocs( s : SymbTrans ) : Seq[SourceLocation] =
    s._1 map { x => sourceLocator.sourceOf( x ).get } sortWith locLT

  private def transLT( a: SymbTrans, b: SymbTrans ): Boolean = seqLocLT( getSortedLocs( a ), getSortedLocs( b ) )
  /**
    * Sorts the transitions lexicographically on the source code information of assignments
    */
  def sourceSort( transitions : Seq[SymbTrans] ) : Seq[SymbTrans] =
    transitions sortWith transLT
}
