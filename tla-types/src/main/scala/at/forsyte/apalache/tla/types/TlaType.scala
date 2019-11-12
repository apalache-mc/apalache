package at.forsyte.apalache.tla.types

/**
  * This class represents the types introduced in our paper.
  *
  * We do not enforce the exact grammar through class hierarchies, but defer the responsibility
  * of defining permissible types to the user.
  */
abstract class TlaType

sealed case class TypeVar( i : Int ) extends TlaType

object StrT extends TlaType
object IntT extends TlaType
object BoolT extends TlaType
sealed case class FunT( domT : TlaType, cdmT : TlaType ) extends TlaType
sealed case class SetT( t : TlaType ) extends TlaType
sealed case class SeqT( t : TlaType ) extends TlaType
sealed case class TupT( ts: TlaType* ) extends TlaType
sealed case class RecT( tmap: TypeMap[String] ) extends TlaType
sealed case class SparseTupT( tmap: TypeMap[Int] ) extends TlaType
sealed case class OperT( domT : TupT, cdmT : TlaType ) extends TlaType
sealed case class PolyOperT( tVars: List[TypeVar], op: OperT ) extends TlaType