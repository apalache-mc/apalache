package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolVar
import at.forsyte.apalache.tla.lir.formulas.EUF.{DefineFun, FunctionVar, UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.IntVar
import at.forsyte.apalache.tla.lir.formulas._
import scalaz.Scalaz._
import scalaz._

package object vmt {
  type ConstSetMapT = Map[String, UninterpretedSort]

  // collects all definitions/declarations that rules may discharge. In principle, this could be a single bucket
  // of Declarations, but for clarity, it's nicer to split them.
  // This should be future-proof, so any State modifications should always use _copy_, as to allow for the addition of
  // other declaration fields later.
  sealed case class SmtDeclarations(
      definedFunctions: Map[String, DefineFun],
      uninterpretedSorts: Set[String],
      uninterpretedLiterals: Map[String, UninterpretedLiteral])

  object SmtDeclarations {
    def init: SmtDeclarations = SmtDeclarations(Map.empty, Set.empty, Map.empty)
  }

  type TermBuilderTemplateT[A] = State[SmtDeclarations, A]
  type TermBuilderT = TermBuilderTemplateT[Term]

  /** Turns a sequence of States into a single State wrapping list of values */
  def cmpSeq[A, S](args: Iterable[State[S, A]]): State[S, List[A]] =
    // Scalaz defines .sequence only over Lists, not Seqs, but we get args (from variadic constructors)
    // as Seq, so there's a bit of back-and-forth conversion happening here.
    args.toList.sequence

  /** Adds a function definition to the internal state collection, and returns that function's Term representation. */
  def storeDefAndUse(funDef: DefineFun): TermBuilderT = State[SmtDeclarations, Term] { s =>
    (s.copy(definedFunctions = s.definedFunctions + (funDef.name -> funDef)), funDef.asVar)
  }

  /**
   * Creates and adds a function definition to the internal state collection, and returns that function's Term
   * representation.
   */
  def defineAndUse(name: String, args: Seq[(String, Sort)], body: Term): TermBuilderT = {
    val funDef = DefineFun(name, args, body)
    storeDefAndUse(funDef)
  }

  /** Adds an uninterpreted sort declaration to the internal state collection. */
  def storeUninterpretedSort(sort: Sort): TermBuilderTemplateT[Unit] = sort match {
    case UninterpretedSort(name) =>
      modify[SmtDeclarations] { s => s.copy(uninterpretedSorts = s.uninterpretedSorts + name) }
    case _ => ().point[TermBuilderTemplateT]
  }

  /**
   * Adds an uninterpreted literal declaration to the internal state collection. If its Sort is not declared yet, or the
   * Term is an uninterpreted variable instead, also adds the sort declaration.
   */
  def storeUninterpretedLiteralOrVar(term: Term): TermBuilderTemplateT[Unit] = term match {
    case l @ UninterpretedLiteral(name, sort) =>
      storeUninterpretedSort(sort).flatMap { _ =>
        modify[SmtDeclarations] { s => s.copy(uninterpretedLiterals = s.uninterpretedLiterals + (name -> l)) }
      }
    case UninterpretedVar(_, sort) => storeUninterpretedSort(sort)
    case _                         => ().point[TermBuilderTemplateT]
  }

  /**
   * Since ['] is not a legal symbol in SMTLIB, we have to choose a convention for the names of primed variables. If `x`
   * is a variable name, then `x^` is the name used to represent `x'` in SMTLIB.
   */
  def VMTprimeName(s: String) = s"$s^"
  // Apply VMTprimeName to NameEx directly
  def renamePrimesForVMT(unprimedNameEx: NameEx): NameEx =
    NameEx(VMTprimeName(unprimedNameEx.name))(unprimedNameEx.typeTag)

  /**
   * VMT uses a named function definition to explicitly annotate which pairs of symbols represent the current- and
   * next-state value of a system variable. If `x` represents the current-state value, and `x^` the next-state value,
   * then `.x` is the name of the binding function.
   */
  def nextName(name: String): String = s".$name"

  /**
   * Creates a `Variable` term, of the appropriate subtype, based on the sort.
   */
  def mkVariable(name: String, sort: Sort): Variable = sort match {
    case IntSort               => IntVar(name)
    case BoolSort              => BoolVar(name)
    case fs: FunctionSort      => FunctionVar(name, fs)
    case us: UninterpretedSort => UninterpretedVar(name, us)
    case s                     => new Variable(name) { override val sort: Sort = s }
  }
}
