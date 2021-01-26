package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.TlaValue
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet, TlaRealSet}
import at.forsyte.apalache.tla.lir.values.TlaRealInfinity

/**
  * Values and operators that are defined in the standard TLA+ library.
  *
  * @author Igor Konnov
  */
object StandardLibrary {

  /**
    * The operators in the following modules are overloaded by the importer, so we exclude their
    * operator definitions from the user modules. (Moreover, the standard modules sometimes contain garbage
    * or complex definitions that should not be analyzed by our tool.)
    */
  val standardModules: Set[String] =
    Set(
      "Naturals",
      "Integers",
      "Sequences",
      "TLC",
      "FiniteSets",
      "Reals",
      "Apalache",
      "Typing"
    )

  val libraryValues: Map[Tuple2[String, String], TlaValue] =
    Map(
      ("Naturals", "Nat") -> TlaNatSet,
      ("Integers", "Int") -> TlaIntSet,
      ("Reals", "Real") -> TlaRealSet,
      ("Reals", "Infinity") -> TlaRealInfinity
    ) ////

  val libraryOperators: Map[Tuple2[String, String], TlaOper] =
    Map(
      ("Naturals", "+") -> TlaArithOper.plus,
      ("Naturals", "-") -> TlaArithOper.minus,
      ("Naturals", "*") -> TlaArithOper.mult,
      ("Naturals", "^") -> TlaArithOper.exp,
      ("Naturals", "<") -> TlaArithOper.lt,
      ("Naturals", ">") -> TlaArithOper.gt,
      ("Naturals", "<=") -> TlaArithOper.le,
      ("Naturals", "\\leq") -> TlaArithOper.le,
      ("Naturals", ">=") -> TlaArithOper.ge,
      ("Naturals", "\\geq") -> TlaArithOper.ge,
      ("Naturals", "%") -> TlaArithOper.mod,
      ("Naturals", "\\div") -> TlaArithOper.div,
      ("Naturals", "..") -> TlaArithOper.dotdot,
      ("Integers", "-.") -> TlaArithOper.uminus,
      ("Reals", "/") -> TlaArithOper.realDiv,
      ("Sequences", "Seq") -> TlaSetOper.seqSet,
      ("Sequences", "Len") -> TlaSeqOper.len,
      ("Sequences", "\\o") -> TlaSeqOper.concat,
      ("Sequences", "Append") -> TlaSeqOper.append,
      ("Sequences", "Head") -> TlaSeqOper.head,
      ("Sequences", "Tail") -> TlaSeqOper.tail,
      ("Sequences", "SubSeq") -> TlaSeqOper.subseq,
      ("Sequences", "SelectSeq") -> TlaSeqOper.selectseq,
      ("FiniteSets", "IsFiniteSet") -> TlaFiniteSetOper.isFiniteSet,
      ("FiniteSets", "Cardinality") -> TlaFiniteSetOper.cardinality,
      ("TLC", "Any") -> TlcOper.any,
      ("TLC", "Assert") -> TlcOper.assert,
      ("TLC", "@@") -> TlcOper.atat,
      ("TLC", ":>") -> TlcOper.colonGreater,
      ("TLC", "JavaTime") -> TlcOper.javaTime,
      ("TLC", "Permutations") -> TlcOper.permutations,
      ("TLC", "RandomElement") -> TlcOper.randomElement,
      ("TLC", "SortSeq") -> TlcOper.sortSeq,
      ("TLC", "TLCEval") -> TlcOper.tlcEval,
      ("TLC", "TLCGet") -> TlcOper.tlcGet,
      ("TLC", "TLCSet") -> TlcOper.tlcSet,
      ("TLC", "ToString") -> TlcOper.tlcToString,
      ("TLC", "Print") -> TlcOper.print,
      ("TLC", "PrintT") -> TlcOper.printT,
      ("Apalache", ":=") -> BmcOper.assign,
      ("Apalache", "Skolem") -> BmcOper.skolem,
      ("Apalache", "Expand") -> BmcOper.expand,
      ("Apalache", "ConstCardinality") -> BmcOper.constCard,
      ("Typing", "AssumeType") -> TypingOper.assumeType,
      ("Typing", "##") -> TypingOper.withType,
      ("Typing", "EmptySet") -> TypingOper.emptySet,
      ("Typing", "EmptySeq") -> TypingOper.emptySeq
    ) ////

  val globalOperators: Map[String, TlaOper] =
    Map[String, TlaOper](
      // TODO: this operator is deprecated, the user should use Typing, add a warning when the type checker is in place
      "<:" -> BmcOper.withType
    ) ////
}
