package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.UID
import at.forsyte.apalache.tla.lir.smt.SmtTools.BoolFormula

/**
  * Typedefs used in this package
  */
package object types {
  type TypeContext = Map[TypeVar, SmtTypeVariable]
  type Binding = Map[String, SmtDatatype]
  type GlobalBinding = Map[String, SmtTypeVariable]
  type Template = Seq[SmtDatatype] => BoolFormula
  type TypeMap[kType] = Map[kType, TlaType]
  type TypeVarAssignment = Map[UID, SmtDatatype]
  type OperatorApplicationStack = List[UID]
  // Because out type-analysis assigns types on a per-call-site basis, we cannot simply
  // assign a type to every UID, because different calls to a polymorphic operator might
  // generate mutually exclusive types to the same UIDs appearing in the body of said operator
  type OperatorContext = Map[OperatorApplicationStack, TypeVarAssignment]

  type TypeAssignment = Map[UID, TlaType]

  object Names {
    val intVarSymb : String = "i"
    val tVarSymb   : String = "f"
    val labelSymb   : String = "l"

    val atIndexName: String = "atIndex"
    val atFieldName: String = "atField"
    val hasIndexName : String = "hasIndex"
    val hasFieldName : String = "hasField"
    val sizeOfName   : String = "sizeOf"
    val rankName   : String = "rank"

    val dtName    : String = "tlaT"
    val intTName  : String = "intT"
    val strTName  : String = "strT"
    val boolTName : String = "boolT"
    val setTName  : String = "setT"
    val seqTName  : String = "seqT"
    val funTName  : String = "funT"
    val operTName : String = "operT"
    val tupTName  : String = "tupT"
    val recTName  : String = "recT"
    val varTName  : String = "varT"
  }

}
