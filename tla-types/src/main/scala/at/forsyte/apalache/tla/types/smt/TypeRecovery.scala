package at.forsyte.apalache.tla.types.smt
import at.forsyte.apalache.tla.types._
import com.microsoft.z3.{DatatypeExpr, Expr, IntNum}

class TypeRecovery(
                    private val tvg : TypeVarGenerator,
                    limits: SpecLimits,
                    typeNarrowerOpt : Option[TypeNarrower]
                  ) {
  import Names._

  private var typeAlloc : Map[Int, TypeVar] = Map.empty
  private val enum = limits.getEnumeration

  def apply( e : Expr ) : TlaType = e match {
    case d : DatatypeExpr =>
      d.getFuncDecl.getName.toString match {
        case `intTName` => IntT
        case `strTName` => StrT
        case `boolTName` => BoolT
        case `setTName` =>
          val Array( setArg ) = d.getArgs
          SetT( apply( setArg ) )
        case `seqTName` =>
          val Array( seqArg ) = d.getArgs
          SeqT( apply( seqArg ) )
        case `funTName` =>
          val Array( dom, cdm ) = d.getArgs
          FunT( apply( dom ), apply( cdm ) )
        case `tupTName` =>
          val Array(sizeEx, indexExs@_*) = d.getArgs
          val size = sizeEx.asInstanceOf[IntNum].getInt
          if ( size < 1 ) {
            TupT()
          } else {
            val Nrelevant = math.min( size, limits.maxIndex )
            val relevantExes = indexExs.take( Nrelevant )
            TupT( relevantExes map apply :_* )
          }

        case `operTName` =>
          val Array(sizeEx, indexExsAndCdm@_*) = d.getArgs
          val size = sizeEx.asInstanceOf[IntNum].getInt
          if ( size < 1 ) {
            OperT( TupT( ), apply( indexExsAndCdm.last ) )
          } else {
            val Nrelevant = math.min( size, limits.maxIndex )
            val relevantExes = indexExsAndCdm.take( Nrelevant )
            val cdmT = apply( indexExsAndCdm.last )
            OperT( TupT( relevantExes map apply : _* ), cdmT )
          }

        case `recTName` =>
          val Array( idEx, fieldExs@_* ) = d.getArgs
          val fieldArr = fieldExs.toArray map apply
          val recMap = limits.fields.map(
            s =>  s -> fieldArr( enum.getIdx( s ) )
          ).toMap
          val broad = RecT( recMap )
          val i = idEx.asInstanceOf[IntNum].getInt
          typeNarrowerOpt.map {
            _.narrow( broad, i )
          } getOrElse broad
        case `varTName` =>
          val Array( iExp ) = d.getArgs
          val i = iExp.asInstanceOf[IntNum].getInt
          // For varT expressions, we must make sure that
          // we assign variables with the same id the same TypeVar.
          // For this, we use typeAlloc.
          val tv = typeAlloc.getOrElse( i, tvg.getUnique )
          typeAlloc += i -> tv
          tv
        case x =>
          throw new IllegalArgumentException( s"$x cannot be evaluated in the model." )
      }
    case x => throw new IllegalArgumentException( s"$x is not a TlaType." )
  }
}
