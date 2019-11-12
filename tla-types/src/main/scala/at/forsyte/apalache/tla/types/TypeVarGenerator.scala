package at.forsyte.apalache.tla.types

/**
  * TypeVarGenerator generates unique TypeVar values on demand.
  *
  * See SignatureGenerator.
  */
class TypeVarGenerator {
  private var idx : Int = 0

  def getUnique : TypeVar = {
    val ret = TypeVar( idx )
    idx += 1
    ret
  }

  def getNUnique( n : Int ) : List[TypeVar] = List.fill( n ) { getUnique }
}
