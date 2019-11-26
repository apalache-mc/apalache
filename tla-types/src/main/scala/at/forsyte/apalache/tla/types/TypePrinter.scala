package at.forsyte.apalache.tla.types

object TypePrinter {
  private val lAngle = "\u2329"
  private val rAngle = "\u232A"
  def apply( t : TlaType ) : String = t match {
    case TypeVar( i ) => s"T$i"
    case `StrT` => "Str"
    case `IntT` => "Int"
    case `BoolT` => "Bool"
    case FunT( dom, cdm ) => s"${apply( dom )} \u2192 ${apply( cdm )}"
    case SetT( s ) => s"Set(${apply( s )})"
    case SeqT( s ) => s"Seq(${apply( s )})"
    case TupT( args@_* ) => s"$lAngle${( args map apply ).mkString( ", " )}$rAngle"
    case RecT( tmap ) =>
      val fields = tmap.toList.sortBy( _._1 ) map {
        case (k, v) => s"$k \u21A6 ${apply( v )}"
      }
      s"[${fields.mkString( ", " )}]"
    case SparseTupT( tmap ) =>
      val fields = tmap.toList.sortBy( _._1 ) map {
        case (k, v) => s"$k \u21A6 ${apply( v )}"
      }
      s"$lAngle${fields.mkString( ", " )}$rAngle"
    case OperT( dom, cdm ) => s"${apply( dom )} \u21D2 ${apply( cdm )}"
    case PolyOperT( ts, oper ) => s"\u2200 ${(ts map apply).mkString(", ")}: ${apply(oper)}"
  }
}
