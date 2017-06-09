package at.forsyte.apalache.tla.lir.plugins.types

/**
  * Created by jkukovec on 4/11/17.
  */

object TotalOrder {
  def apply( lhs : ConstMemCell, rhs : ConstMemCell ) : Boolean = {

    (lhs, rhs) match {
      case ( BoolCell(x), BoolCell(y) ) => x < y // false < true
      case ( BoolCell(_), _ ) => true
      case ( _, BoolCell(_) ) => false

      case ( IntCell(x), IntCell(y) ) => x < y
      case ( IntCell(_), _ ) => true  // RHS is not BoolCell by case priority
      case ( _, IntCell(_) ) => false // LHS is not BoolCell by case priority

      case ( StrCell(x), StrCell(y) ) => x < y
      case ( StrCell(_), _ ) => true
      case ( _, StrCell(_) ) => false

      case ( SetCell( elems1@_* ), SetCell( elems2@_* ) ) => {

        val distinct1 = elems1.distinct
        val distinct2 = elems2.distinct

        val l1 = distinct1.size
        val l2 = distinct2.size

        if( l1 < l2 ) true
        else if ( l2 < l1 ) false
        else {
          // If both sides are sets of the same size, they are both internally well ordered.
          // We can treat them as tuples and compare lexicographically.
          val pairsOrdered = distinct1.sortWith( TotalOrder(_,_) ).zip(
                             distinct2.sortWith( TotalOrder(_,_) ) )

          // Either lhs(1) < rhs(1) or lhs(1) == rhs(1) and lhs(2) < rhs(2), and so on.
          // In general, lhs < rhs if for the first index i, for which lhs(i) != rhs(i) it holds
          // that lhs(i) < rhs(i).
          val firstUnequalPair= pairsOrdered.find( pa => pa._1 != pa._2 )

          // If lhs == rhs, no such index should exist, otherwise, we test for total order.
          firstUnequalPair.exists( pa => TotalOrder( pa._1 , pa._2) )
        }
      }
      case ( SetCell(_), _ ) => true
      case ( _, SetCell(_) ) => true

      case _ => false
    }
  }

}

abstract class MemCell

case class VarCell( v : String ) extends MemCell

abstract class ConstMemCell extends MemCell{
  override def equals( other: Any ) : Boolean = {
    (this, other) match {
      case ( BoolCell(x), BoolCell(y) ) => x == y
      case ( IntCell(x), IntCell(y) ) => x == y
      case ( StrCell(x), StrCell(y) ) => x == y
      case ( SetCell( elems1@_* ), SetCell( elems2@_* ) ) => {
        // A = B iff \A x \in A . x \in B /\ \A y \in B . y \in A
        // suboptimal, because we cannot assume elems(1/2) is sorted. If ever enforced, replace with specialized check
        elems1.forall( x => elems2.contains( x ) ) && elems2.forall( y => elems1.contains( y ) )
      }
      case _ => false
    }
  }

  def <(other : ConstMemCell) : Boolean = TotalOrder(this,other)

}

abstract class GroundCell extends ConstMemCell

case class IntCell( i: Int ) extends GroundCell
case class BoolCell( b: Boolean ) extends GroundCell
case class StrCell( s: String ) extends GroundCell

case class SetCell( elements: ConstMemCell* ) extends ConstMemCell {
  def size: Int = elements.size
  def removeDuplicates(): SetCell = SetCell( elements.distinct:_* )
  def normalized() : SetCell = SetCell( elements.distinct.sortWith( TotalOrder(_,_) ):_* )
  def <=( other: SetCell ) : Boolean = true
}
