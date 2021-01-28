package at.forsyte.apalache.tla.lir.aux

abstract class ExceptionOrValue[T] {
  def getOrThrow : T = this match {
    case FailWith( e ) => throw e
    case SucceedWith( v ) => v
  }
}

sealed case class FailWith[T]( e: Exception ) extends ExceptionOrValue[T]
sealed case class SucceedWith[T]( value: T ) extends ExceptionOrValue[T]
