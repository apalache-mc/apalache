
package at.forsyte.apalache.tla.lir

import scala.collection.immutable.Set
import scala.collection.immutable.Map
import scala.collection.immutable.Seq



import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB

package object assignments{

  abstract class BoolFormula
  case class True() extends BoolFormula
  case class False() extends BoolFormula
  case class And( args : BoolFormula* ) extends BoolFormula
  case class Or( args : BoolFormula* ) extends BoolFormula
  case class Variable( id: Int ) extends BoolFormula

  // Empty and cluases are never generated
  def simplify(phi: BoolFormula ) : BoolFormula = {
    phi match {
      case And( args@_*) => {
        val newargs = args.map(simplify)
        if ( newargs.contains( False() ) )
          False()
        else
          And( newargs:_* )
      }
      case Or( args@_*) => {
        val newargs = args.map(simplify).filterNot( _ == False() )
        newargs.size match {
          case 0 => False()
          case 1 => newargs.head
          case _ =>Or( newargs:_* )
        }
      }
      case _ => phi
    }
  }

  private def delta( v: NameEx )( phi: OperEx ) : BoolFormula = {
    // assume well-formedndess, i.e. only and/or/in
    phi.oper match {
      case TlaBoolOper.and => Or( phi.args.map( arg => delta(v)( arg.asInstanceOf[OperEx] ) ):_* )
      case TlaBoolOper.or => And( phi.args.map( arg => delta(v)( arg.asInstanceOf[OperEx] ) ):_* )
      case TlaSetOper.in => {
        phi.args.head match {
          case OperEx( TlaActionOper.prime, NameEx( name ) ) => {
            if( v == NameEx( name ) )
              Variable( phi.ID.id )
            else
              False()
          }
          case _ => False()
        }
      }
      case _ => False()
    }
  }

  // assume i in rage for sanity
  private def lvar( i : Int ) : NameEx = UniqueDB.apply( UID( i ) ).
    head.asInstanceOf[OperEx].args.
    head.asInstanceOf[OperEx].args.
    head.asInstanceOf[NameEx]

  private def findPrimes( ex : TlaEx ) : Set[NameEx] = {
    ex match {
      case OperEx( TlaActionOper.prime, NameEx(n) ) => Set(NameEx(n))
      case OperEx( _, args@_* ) => args.map( findPrimes ).fold( Set[NameEx]() ){ (a,b) => a ++ b }
      case _ => Set[NameEx]()
    }
  }
  private def rvars( i : Int ) : Set[NameEx] = {
    findPrimes(
      UniqueDB(UID(i)).head.asInstanceOf[OperEx].args.tail.head // 2nd arg is the RHS
    )
  }

  def sqsubset( i: Int, j: Int ): Boolean = rvars( j ) contains lvar( i )

  // assume no equalities, all of the form a \in B
  protected def massProcess( p_phi : TlaEx, p_vars: Set[NameEx] )
    : ( Set[(Int,Int)], Map[NameEx,BoolFormula] ) = {
    val ret = innerMassProcess(p_phi,p_vars)
    (ret._2, ret._4.map( pa => (pa._1, simplify(pa._2) ) ) )
  }
  protected def innerMassProcess( p_phi : TlaEx, p_vars: Set[NameEx] )
                : ( Set[Int], Set[(Int,Int)], Set[(Int,Int)], Map[NameEx,BoolFormula] ) = {

    val defaultMap = ( for {v <- p_vars} yield (v, False()) ).toMap
    val defaultArgs = ( Set[Int](), Set[(Int,Int)](), Set[(Int,Int)](), defaultMap )

    p_phi match {
      case OperEx(oper, args@_*) =>
        oper match{
          case TlaBoolOper.and | TlaBoolOper.or =>
            // OKCheck : simply recurse, take forall
            // label : simply recurse, do foreach
            // D : All unprocessed children on all branches are dependent/indep.

            val processedArgs = args.map( innerMassProcess( _, p_vars) )

            // CONTINUE HERE
            val newMapArgs =
              ( for { v <- p_vars } yield
                ( v,
                  processedArgs.map(
                    tpl => tpl._4
                  ).map(
                    _.get(v)
                  ).filterNot( _.isEmpty ).map(
                    _.head
                  )
                )
              ).toMap

            val ( seen, depSet, indepSet, _ ) = processedArgs.fold(
              defaultArgs
            ){
              ( a,b ) => ( a._1 ++ b._1,
                           a._2 ++ b._2,
                           a._3 ++ b._3,
                           defaultArgs._4 // irrelevant
              )
            }

            val newMap : Map[NameEx,BoolFormula] =
              (
                for { v <- p_vars }
                  yield ( v,
                          if (oper == TlaBoolOper.and)
                            Or(newMapArgs(v):_*)
                          else
                            And(newMapArgs(v):_*)
                        )
              ).toMap


            val S : Set[(Int,Int)] = for { x <- seen; y <- seen } yield (x,y)

            // all unprocessed pairs are dep., guaranteed n1 > n0
            oper match {
              case TlaBoolOper.and => ( seen, S -- indepSet, indepSet, newMap )
              case TlaBoolOper.or  => ( seen, depSet, S -- depSet, newMap )
            }
          case TlaSetOper.in =>
            args.head match {
              case OperEx( TlaActionOper.prime, nameEx ) => {
                val n : Int = p_phi.ID.id
                val newmap = ( for { v <- p_vars } yield (v, if( nameEx == v ) Variable( n ) else False() ) ).toMap
                ( Set[Int](n), Set[(Int,Int)]( (n,n) ), Set[(Int,Int)](), newmap )
              }
              case _ => defaultArgs // not an assignment for sure
            }
          case _ => defaultArgs
        }
        // no info, we KNOW toplevel call is on an OperEx
      case _ => defaultArgs
    }
  }


  def apply( p_vars: Set[NameEx],  p_phi : OperEx ) : Option[Seq[TlaEx]] = {

    val ( deps, deltas ) = massProcess(p_phi, p_vars)

    val simpleDeltas = ( for {v <- p_vars} yield ( v, simplify( deltas(v) ) ) ).toMap

    print( "Dep. ["+ deps.size + "]: " + deps )
    print("\n")
    print( "Deltas: [" + simpleDeltas.size + "]: "+ simpleDeltas.mkString("\n" ) )

    val D_sqss = deps.filter( pa =>  sqsubset( pa._1, pa._2 ) )

    print("\n")
    print( "D_sqss ["+ D_sqss.size + "]: " + D_sqss )

    //val deltas = p_vars.map( v => ( v.name, simplify(delta(v)(p_phi)) ) )

//    print( "\nDeltas: \n" + deltas.mkString("\n"))

    def buildsmt( vars : Set[NameEx], depSet : Set[(Int, Int)] ) : String = {
      ""
    }

    val spec = buildsmt( p_vars, D_sqss )

    // TODO:
    // - Construct Phi_S

    return Some( Seq() )
  }

}


