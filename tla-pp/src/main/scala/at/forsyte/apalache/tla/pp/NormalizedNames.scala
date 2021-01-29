package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}

/**
  * Normalized names for various operator definitions that are produced by pre-processing.
  */
object NormalizedNames {
  val INIT_PREFIX = "Init$"
  val NEXT_PREFIX = "Next$"
  val CONST_INIT = "CInit$0"
  val VC_INV_PREFIX = "VCInv$"
  val VC_NOT_INV_PREFIX = "VCNotInv$"
  val VC_TEMPORAL_PROP_PREFIX = "VCTemporal$"

  // the names of the options that capture the critical specification pieces
  val STANDARD_OPTION_NAMES = Seq("init", "cinit", "next", "inv", "temporalProps")

  /**
    * Extract operator names from the standard option names.
    * @param options the options object
    * @return
    */
  def userOperatorNamesFromOptions(options: PassOptions): List[String] = {
    // first, get the operators whose names are passed as single strings
    val single: List[String] = List("init", "cinit", "next").
      flatMap(options.get[String]("checker", _))
    // second, get the operators whose names are passed as lists of strings
    val multiple: List[String] = List("inv", "temporalProps").
      flatMap(options.get[List[String]]("checker", _)).
      flatten
    single ++ multiple
  }

  /**
    * Has been an operator declaration produced by the VCGenerator
    * @param decl an operator declaration
    * @return true, if the operator name matches the VC pattern
    */
  def isVC(decl: TlaDecl): Boolean = {
    decl.isInstanceOf[TlaOperDecl] &&
      decl.asInstanceOf[TlaOperDecl].formalParams.isEmpty &&
      (decl.name.startsWith(VC_INV_PREFIX) || decl.name.startsWith(VC_NOT_INV_PREFIX))
  }

  /**
    * Does a declaration present a temporal property.
    * (Temporal properties are not supported by Apalache yet.)
    *
    * @param decl an operator declaration
    * @return true, if the operator name starts with the VC_TEMPORAL_PROP_PREFIX
    */
  def isTemporalVC(decl: TlaDecl): Boolean = {
    decl.isInstanceOf[TlaOperDecl] &&
      decl.asInstanceOf[TlaOperDecl].formalParams.isEmpty &&
      decl.name.startsWith(VC_TEMPORAL_PROP_PREFIX)
  }

  /**
    * Does an operator define the constant initializer (there is only one).
    *
    * @param decl an operator declaration
    * @return true, if the operator is a constant initializer
    */
  def isConstInit(decl: TlaDecl): Boolean = {
    decl.isInstanceOf[TlaOperDecl] &&
      decl.asInstanceOf[TlaOperDecl].formalParams.isEmpty &&
      decl.name == CONST_INIT
  }

  /**
    * Does an operator define an init predicate (there may be several).
    *
    * @param decl an operator declaration
    * @return true, if the operator is a state initializer
    */
  def isInit(decl: TlaDecl): Boolean = {
    decl.isInstanceOf[TlaOperDecl] &&
      decl.asInstanceOf[TlaOperDecl].formalParams.isEmpty &&
      decl.name.startsWith(INIT_PREFIX)
  }

  /**
    * Does an operator define a transition predicate (there may be several).
    *
    * @param decl an operator declaration
    * @return true, if the operator is a transition predicate
    */
  def isNext(decl: TlaOperDecl): Boolean = {
    decl.isInstanceOf[TlaOperDecl] &&
      decl.asInstanceOf[TlaOperDecl].formalParams.isEmpty &&
      decl.name.startsWith(NEXT_PREFIX)
  }
}
