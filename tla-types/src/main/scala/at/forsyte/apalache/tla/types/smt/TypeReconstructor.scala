package at.forsyte.apalache.tla.types.smt

import at.forsyte.apalache.tla.types._
import com.microsoft.z3.{DatatypeExpr, Expr, IntNum}

/**
  * TypeReconstructor allows us to recover TlaTypes from z3 Expr values, containing our custom datatype expressions
  */
class TypeReconstructor(
                         idxFun : (Int, Int) => Option[Expr],
                         fieldFun : (Int, Int) => Option[Expr],
                         sizeFun : Int => Int,
                         strEnumerator : StringEnumerator
                       ) {
  import Names._

  private val tvg       : TypeVarGenerator  = new TypeVarGenerator
  private var typeAlloc : Map[Int, TypeVar] = Map.empty

  def apply( e : Expr ) : TlaType = e match {
    case d : DatatypeExpr =>
      d.getFuncDecl.getName.toString match {
        case `intTName` => IntT
        case `strTName` => StrT
        case `boolTName` => BoolT
        case `funTName` =>
          val Array( dom, cdm ) = d.getArgs
          val domT = apply( dom )
          val cdmT = apply( cdm )
          FunT( domT, cdmT )
        case `operTName` =>
          val Array( dom, cdm ) = d.getArgs
          val domT = apply( dom )
          val cdmT = apply( cdm )
          // Operators always have tuples as domains
          assert( domT.isInstanceOf[TupT] )
          OperT( domT.asInstanceOf[TupT], cdmT )
        case `setTName` =>
          val Array( setArg ) = d.getArgs
          SetT( apply( setArg ) )
        case `seqTName` =>
          val Array( seqArg ) = d.getArgs
          SeqT( apply( seqArg ) )
        case `tupTName` =>
          val Array( iExp ) = d.getArgs
          val i = iExp.asInstanceOf[IntNum].getInt
          val size = sizeFun( i )
          // For tuples or sparse tuples, we know how many indices we must check from the size function
          val tupArgs = for {
            j <- 0 until size
            // In the case of sparse tuples, any index that isn't known from the
            // idxFun gets assigned a unique type variable
          } yield idxFun( i, j ).map( apply ).getOrElse( tvg.getUnique )
          TupT( tupArgs : _* )
        case `recTName` =>
          val Array( iExp ) = d.getArgs
          val i = iExp.asInstanceOf[IntNum].getInt
          // For records, unlike tuples, we don't have an explicit upper bound on the number of
          // fields to check. Instead we check all record fields that appear in the specification
          // and keep those for which fieldFun is defined.
          val recMap = for {
            jStr <- strEnumerator.allStrings
            jId <- strEnumerator.stringToId( jStr )
            v <- fieldFun( i, jId )
          } yield jStr -> apply( v )
          RecT( recMap.toMap )

        case `varTName` =>
          val Array( iExp ) = d.getArgs
          val i = iExp.asInstanceOf[IntNum].getInt
          // For varT expressions, we must make sure that
          // we assign variables with the same id the same TypeVar.
          // For this, we use typeAlloc.
          val tv = typeAlloc.getOrElse( i, tvg.getUnique )
          typeAlloc += i -> tv
          tv

        case _ => throw new IllegalArgumentException( "..." )
      }
    case _ => throw new IllegalArgumentException( "..." )
  }
}
