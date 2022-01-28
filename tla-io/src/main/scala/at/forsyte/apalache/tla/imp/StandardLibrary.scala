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
   * Library values are translated to the IR values.
   */
  val libraryValues: Map[Tuple2[String, String], TlaValue] =
    Map(
        ("Naturals", "Nat") -> TlaNatSet,
        ("Integers", "Int") -> TlaIntSet,
        ("Reals", "Real") -> TlaRealSet,
        ("Reals", "Infinity") -> TlaRealInfinity,
    ) ////

  /**
   * Library operators are translated to the IR operators.
   */
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
        ("Apalache", ":=") -> ApalacheOper.assign,
        ("Apalache", "Gen") -> ApalacheOper.gen,
        ("Apalache", "Skolem") -> ApalacheOper.skolem,
        ("Apalache", "Expand") -> ApalacheOper.expand,
        ("Apalache", "ConstCardinality") -> ApalacheOper.constCard,
        ("Apalache", "FunAsSeq") -> ApalacheOper.funAsSeq,
        ("Apalache", "FoldSet") -> ApalacheOper.foldSet,
        ("Apalache", "FoldSeq") -> ApalacheOper.foldSeq,
    ) ////

  /**
   * The names of the modules that should be wired by Apalache with custom modules.
   *
   * @see at.forsyte.apalache.tla.imp.SanyNameToStream
   */
  val wiredModules: Map[String, String] =
    Map(
        "TLC.tla" -> "__rewire_tlc_in_apalache.tla",
    ) ////

  /**
   * Global operators are translated to IR operators. However, we advise against this practice:
   * TLA+ does not allow one to override the same operator in different modules.
   */
  val globalOperators: Map[String, TlaOper] =
    Map[String, TlaOper](
        // This operator is deprecated and should not be used.
        // We still parse it, so the type checker can complain about it.
        "<:" -> ApalacheOper.withType,
    ) ////
}
