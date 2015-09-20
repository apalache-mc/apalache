package at.forsyte.apalache.tla.ir

/**
 * An entity kind, which mirrors the kind of a tla2sany.semantic.SemanticNode.
 *
 * @see tla2sany.semantic.SemanticNode of TLA Toolbox
 *
 * @author konnov
 */
object Kind extends Enumeration {
                   // value 1 is used for a module
  val Const           = Value(2,  "Constant")
  val Var             = Value(3,  "Variable")
  val BoundSym        = Value(4,  "BoundSymbol")
  val UserOp          = Value(5,  "UserDefinedOperator")
  val ModInst         = Value(6,  "ModuleInstance")
  val BuiltinOp       = Value(7,  "BuiltinOperator")
  val OpArg           = Value(8,  "OperatorArgument")
  val OpApp           = Value(9,  "OperatorApplication")
  val LetIn           = Value(10, "LetIn")
  val FormalParam     = Value(11, "FormalParam")
  val Theorem         = Value(12, "Theorem")
  val SubstIn         = Value(13, "SubstIn")
  val AssumeProve     = Value(14, "AssumeProve")
                      // value 15 is missing in SemanticNode
  val Numeral         = Value(16, "Numeral")
  val Decimal         = Value(17, "Decimal")
  val String          = Value(18, "String")
  val AtNode          = Value(19, "AtNode")
  val Assume          = Value(20, "Assume")
  val Instance        = Value(21, "Instance")
  val NewSymb         = Value(22, "NewSymb") // instance statement or definition
  val ThmOrAssumpDef  = Value(23, "ThmOrAssump")
}
