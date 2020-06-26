package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, BoolFormula, Or}

object TypePrinter {
  private val lAngle = "\u2329"
  private val rAngle = "\u232A"
  import Names._

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
    case PolyOperT( ts, oper ) => s"\u2200 ${( ts map apply ).mkString( ", " )}: ${apply( oper )}"
  }

  def apply( dt: SmtDatatype ) : String = dt match {
    case SmtTypeVariable( i ) => s"$tVarSymb$i"
    case `int` => "intT"
    case `str` => "strT"
    case `bool` => "boolT"
    case set( s ) => s"set(${apply( s )})"
    case seq( s ) => s"seq(${apply( s )})"
    case fun( dom, cdm ) => s"fun(${apply(dom)},${apply(cdm)})"
    case tup( size, idxs ) =>
      val sizeStr = size match {
        case SmtIntVariable(i) => s"$intVarSymb$i"
        case SmtKnownInt(i) => s"$i"
      }
      s"tup($sizeStr, ${( idxs map apply ).mkString( ", " )})"
    case rec( SmtIntVariable(i), fields) => s"rec($intVarSymb$i, ${( fields map apply ).mkString( ", " )})"
    case oper( domTup, ret ) => s" oper(${apply(domTup)}, ${apply(ret)})"
    case _ => ""
  }

  def apply( bf : BoolFormula ) : String = bf match {
    case And( args@_* ) =>
      args map { a => s"${apply( a )}" } mkString " \u2227 "
    case Or( args@_* ) =>
      args map { a => s"${apply( a )}" } mkString " \u2228 "
    case ge( SmtIntVariable( i ), minSize ) =>
      s"$intVarSymb$i \u2265 $minSize"
    case Eql( a, b ) =>
      s"${apply(a)} = ${apply(b)}"
  }
}
