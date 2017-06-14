package at.forsyte.apalache.tla.lir.plugins.types

abstract class Type{
  def <=( other : Type ): Boolean =
    /** reflexive */
    if( this == other )
      return true
    else
      (this, other) match {
        /** the empty set is a subtype of all set types */
        case ( FinSet( tau, SetCell()  ), taus : SetType ) => true

        /** finite sets are subtypes if the types and the sets match */
        case ( FinSet( tau1, v1 ),FinSet( tau2, v2 ) ) => tau1 <= tau2 && v1 <= v2

        /** Records are preserved under field order shuffle and records with more fields are subtypes of those with fewer */
        case ( Rec( fields1 ), Rec( fields2 ) ) => fields2.keySet.subsetOf(fields1.keySet)

        /** Function subtyping is covariant wrt codomains and contravariant wrt domains */
        case ( Fun( taus1, tau1 ), Fun( taus2, tau2 ) ) => taus2 <= taus1 && tau1 <= tau2

        /** Sum types */
        case ( s1: Sum, s2: Sum ) => {
          val n1 = s1.normalized()
          val n2 = s2.normalized()
          n1.taus.forall( n2.taus.contains(_) ) // Move to sets for O( log n ) contains instead of O(n) ?
        }
        case ( tau, s: Sum ) => s.normalized().taus.contains(tau)



        //        case ( FinSet( taus1, _ ), PowSet(taus2) ) => taus1 == taus2
//        case ( FinSet( Fun(a1,b1), _ ), FunSet(a2,b2)) => (a1,b1) == (a2,b2)
//        case ( FinSet( _, SetCell() ), taus : SetType ) => true
        case _ => false
      }

}

abstract class SetType extends Type{
  def elementType : Type
}

case class TBool( ) extends Type
case class TInt( ) extends Type
case class TString( ) extends Type

case class Fun( taus: SetType, tau: Type ) extends Type

case class Sum( taus: Type* ) extends Type{
  /** We want sums in a way that normalizes to a bracket-less form, due to associativity */
  def isNormal() : Boolean = taus.forall( !_.isInstanceOf[Sum] )

  def normalized() : Sum = {
    def mkseq( tau: Type ): Seq[ Type ] = {
      tau match {
        case sum: Sum => sum.taus
        case nosum => Seq( nosum )
      }
    }
    if( isNormal() ) {
      this
    }
    else {
      val newargs = for ( tau <- taus; x <- mkseq( tau ) ) yield x
      Sum( newargs:_* )
    }
  }
}

case class TypeVar() extends Type

case class FinSet( tau: Type, v: SetCell ) extends SetType{
  override def elementType: Type = tau
}
//case class FunSet( taus: SetType, tau: Type ) extends SetType{
//  override def elementType: Type = Fun( taus, tau )
//}
//case class PowSet( taus : SetType ) extends  SetType{
//  override def elementType: Type = taus
//}

case class FinSeq( tau : Type, v : SetCell ) extends Type

case class Rec( fields: Map[String, Type] ) extends Type

case class Tuple( taus: Type* ) extends Type

/** Free constant generator */

/** Convenience ctors */

object PowSet{
  protected def powerset( setCell: SetCell ) : SetCell = {
    val n = setCell.elements.size
    var newargs : Seq[SetCell] = Seq()
    for ( i <- 0 to n ){
      var cellSeq : Seq[ConstMemCell] = Seq()
      var binI = Integer.toBinaryString( i )
      while ( binI.length < n ) binI = "0" + binI
      for( (el, ind) <- setCell.elements.zipWithIndex ){
        if( binI.charAt( ind ) == '1' ) cellSeq = cellSeq :+ el
      }
      newargs = newargs :+ SetCell( cellSeq:_* )
    }
    SetCell( newargs:_* )
  }
  def apply( finSet: FinSet ): FinSet ={
    FinSet( finSet, powerset( finSet.v ) )
  }
}

object FunSet{
  def apply( domain: FinSet, codomain: FinSet ) : FinSet = {

  }
}
