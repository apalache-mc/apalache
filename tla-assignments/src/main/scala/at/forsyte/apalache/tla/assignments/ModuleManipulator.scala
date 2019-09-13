package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{FormalParam, TlaEx, TlaModule, TlaOperDecl}

/**
  * Moving away from SpecWithTransitions ModuleManipulator allows us to re-insert special TlaEx
  * back into a TlaModule, as operators with special names. All such operators are suffixed with
  * `suffix`, which is a string disallowed by the TLA+ operator naming rules.
  */
object ModuleManipulator {
  val suffix: String = "$"

  object defaultNames {
    val initDefaultName        : String = "Init"
    val nextDefaultName        : String = "Next"
    val cinitDefaultName       : String = "CInit"
    val notInvDefaultName      : String = "NInv"
    val notInvPrimeDefaultName : String = "NInvP"
    val renamingPrefix         : String = "Renamed"
  }
  def declsFromTransitionBodies( transitionOperName : String, transitions : Seq[TlaEx] ) : Seq[TlaOperDecl] =
    transitions.zipWithIndex map { case (t, i) =>
      // Name + $ + index is guaranteed to not clash with existing names, as
      // $ is not an allowed symbol in TLA
      TlaOperDecl( s"$transitionOperName$suffix$i", List.empty[FormalParam], t )
    }


  def declsFromTransitions( transitionOperName : String, transitions : Seq[SymbTrans] ) : Seq[TlaOperDecl] =
    // drop selections because of lacking implementation further on
    declsFromTransitionBodies( transitionOperName, transitions map { _._2 } )

  def optionalOperDecl( newOperName: String, optionalBody: Option[TlaEx] ) : Option[TlaOperDecl] =
    optionalBody map { b =>
      TlaOperDecl( s"$newOperName$suffix", List.empty[FormalParam], b )
    }

  def insertTransitions( module : TlaModule, transitionOperName : String, transitions : Seq[SymbTrans] ) : TlaModule = {
    new TlaModule( module.name, declsFromTransitions( transitionOperName, transitions ) ++ module.declarations )
  }

  def optionalInsertOperator( module: TlaModule, newOperName: String, optionalBody: Option[TlaEx] ) : TlaModule =
    optionalOperDecl( newOperName, optionalBody ) map { d =>
      new TlaModule( module.name, d +: module.declarations )
    } getOrElse module

  /**
    * After re-inserting the transitions into the spec as operators with special names,
    * we want to extract them again when we need them. We know all symbolic transition names
    * (for init or next, depending on `baseName`) contain the `SymbolicTransitionInserter.suffix`
    * string, that distinguishes them from normal operators.
    */
  def getTransitionsFromSpec( module: TlaModule, baseName: String ) : Seq[TlaEx] =
    module.operDeclarations.withFilter {
      _.name.startsWith( s"$baseName$suffix" ) // transitions end in 0,1,...
    } map {
      _.body
    }

  def getOperatorOption( module: TlaModule, operBaseName: String ) : Option[TlaEx] =
    module.operDeclarations.find {
      _.name == s"$operBaseName$suffix"
    } map {
      _.body
    }
}
