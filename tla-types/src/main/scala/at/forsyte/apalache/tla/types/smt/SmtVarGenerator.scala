package at.forsyte.apalache.tla.types.smt

import at.forsyte.apalache.tla.types.{SmtIntVariable, SmtTypeVariable, SmtVariable}

/**
  * Generator for fresh SMT variables, of the TlaType datatype or integer variety.
  */
class SmtVarGenerator {
  private var idx_t : Int = 0
  private var idx_i : Int = 0

  def getFresh : SmtTypeVariable = {
    val ret = SmtTypeVariable( idx_t )
    idx_t += 1
    ret
  }

  def getNFresh( n : Int ) : List[SmtTypeVariable] = List.fill( n ) {
    getFresh
  }

  def getFreshInt : SmtIntVariable = {
    val ret = SmtIntVariable( idx_i )
    idx_i += 1
    ret
  }

  def getNFreshInt( n : Int ) : List[SmtIntVariable] = List.fill( n ) {
    getFreshInt
  }

  def allVars : Seq[SmtVariable] =
    ( 0 until idx_i map SmtIntVariable ) ++ ( 0 until idx_t map SmtTypeVariable )

}
