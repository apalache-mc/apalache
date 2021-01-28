package at.forsyte.apalache.tla.types

abstract class TlaType

sealed case class TypeVar( i : Int ) extends TlaType

object StrT extends TlaType
object IntT extends TlaType
object BoolT extends TlaType
sealed case class FunT( domT : TlaType, cdmT : TlaType ) extends TlaType
sealed case class SetT( t : TlaType ) extends TlaType
sealed case class SeqT( t : TlaType ) extends TlaType
sealed case class TupT( ts: TlaType* ) extends TlaType
sealed case class KvPair[kType]( k: kType, v: TlaType )
sealed case class RecT( ts: KvPair[String]* ) extends TlaType
sealed case class SparseTupT( ts: KvPair[Int]* ) extends TlaType
sealed case class OperT( domT : TupT, cdmT : TlaType ) extends TlaType
sealed case class PolyOperT( tVars: List[TypeVar], op: OperT )