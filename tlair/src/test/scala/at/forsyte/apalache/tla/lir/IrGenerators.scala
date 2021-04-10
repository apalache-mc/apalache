package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen
import org.scalacheck.Gen.{choose, const, identifier, listOf, listOfN, lzy, oneOf, resize, sized}

/**
 * <p>Generators of TLA expressions and declarations to enable testing of our code with Scalacheck.
 * The current implementation respects operator arity but it may disrespect the expected structure of the arguments,
 * which is usually documented in Javadoc. In the future, we may want to enforce the structure by one of the following
 * solutions: (1) By adding preconditions to the constructors of the IR operators, or (2) by throwing
 * `MalformedTlaError`.</p>
 *
 * <p>Assumptions and limitations:</p>
 *
 * <ol>
 * <li>The current implementation of the generators works best for the code that is unaware of the semantics
 * of TLA+ operators.</li>
 *
 * <li>Our generators neither produce nor apply higher-order operators.</li>
 *
 * <li>The generators tag the produced expressions with either Untyped() or Typed[Int](i) for a random integer value,
 * which should be sufficient for checking that the types are correctly propagated.</li>
 * </ol>
 *
 * @author Igor Konnov
 */
trait IrGenerators {

  // an internal representation of operator signatures (for user-defined operators).
  case class UserOperSig(name: String, nparams: Int)

  // an internal context of the generated operator definitions
  type UserContext = Seq[UserOperSig]

  /**
   * An empty user context.
   */
  val emptyContext: UserContext = Seq[UserOperSig]()

  /**
   * The maximal number of arguments in user-defined operators and built-in operators.
   */
  val maxArgs: Int = 4

  /**
   * The maximal number of declarations per a LET-IN definition. Two is a good choice: It is large enough to capture
   * the bugs where only one declaration is processed.
   */
  val maxDefsPerLetIn: Int = 2

  /**
   * The maximal number of declarations (constants, variables, operators, assumptions) per module.
   */
  val maxDeclsPerModule: Int = 10

  /**
   * The list of the most basic operators that are defined in TlaOper.
   */
  val simpleOperators = List(TlaOper.eq, TlaOper.ne, TlaOper.chooseBounded, TlaOper.apply)

  /**
   * The list of arithmetic operators that are defined in TlaArithOper.
   */
  val arithOperators = List(TlaArithOper.div, TlaArithOper.dotdot, TlaArithOper.exp, TlaArithOper.ge, TlaArithOper.gt,
      TlaArithOper.le, TlaArithOper.lt, TlaArithOper.minus, TlaArithOper.mod, TlaArithOper.mult, TlaArithOper.plus,
      TlaArithOper.uminus)

  /**
   * The list of the most basic operators that are defined in TlaOper.
   */
  val setOperators = List(TlaSetOper.cap, TlaSetOper.cup, TlaSetOper.enumSet, TlaSetOper.filter, TlaSetOper.funSet,
      TlaSetOper.in, TlaSetOper.notin, TlaSetOper.map, TlaSetOper.powerset, TlaSetOper.recSet, TlaSetOper.seqSet,
      TlaSetOper.setminus, TlaSetOper.subseteq, TlaSetOper.times, TlaSetOper.union)

  def genTypeTag: Gen[TypeTag] = for {
    i <- arbitrary[Int]
    tt <- oneOf(Untyped(), Typed[Int](i))
  } yield tt

  /**
   * Generate an integer literal.
   *
   * @return a generator of `ValEx(TlaInt(_))`.
   */
  def genInt: Gen[ValEx] = for {
    i <- arbitrary[Int]
    tt <- genTypeTag
  } yield ValEx(TlaInt(BigInt(i))).withTag(tt)

  /**
   * Generate a Boolean literal.
   *
   * @return a generator of `ValEx(TlaBool(_))`.
   */
  def genBool: Gen[ValEx] = for {
    b <- arbitrary[Boolean]
    tt <- genTypeTag
  } yield ValEx(TlaBool(b)).withTag(tt)

  /**
   * Generate a string literal. We always generate identifiers.
   *
   * @return a generator of `ValEx(TlaStr(_))`.
   */
  def genStr: Gen[ValEx] = for {
    s <- identifier
    tt <- genTypeTag
  } yield ValEx(TlaStr(s)).withTag(tt)

  /**
   * Generate a value expression.
   *
   * @return a generator of `ValEx(_)`.
   */
  def genValEx: Gen[ValEx] =
    oneOf(genInt, genBool, genStr, const(ValEx(TlaBoolSet)), const(ValEx(TlaIntSet)), const(ValEx(TlaNatSet)))

  /**
   * Generate a name expression.
   *
   * @return a generator of `NameEx(_)`.
   */
  def genNameEx: Gen[NameEx] = for {
    s <- identifier
    tt <- genTypeTag
  } yield NameEx(s).withTag(tt)

  /**
   * Generate an application of a user-defined operator.
   *
   * @param ctx a context of user-defined operators
   * @return a generator that produces applications of user-defined operators
   */
  def genOperApply(exGen: UserContext => Gen[TlaEx])(ctx: UserContext): Gen[TlaEx] = sized { size =>
    for {
      declNo <- choose(0, ctx.size - 1)
      decl = ctx(declNo)
      argGen = resize(size - 1, exGen(ctx))
      args <- argsByArity(argGen)(FixedArity(decl.nparams))
      tt <- genTypeTag
    } yield OperEx(TlaOper.apply, NameEx(decl.name) +: args: _*).withTag(tt)
  }

  /**
   * Generate a let-in expression that declares 1..maxDefsPerLetIn operators.
   *
   * @param exGen a generator of TLA expressions
   * @param ctx   a context of user-defined operators
   * @return a generator of let-in definitions
   */
  def genLetInEx(exGen: UserContext => Gen[TlaEx])(ctx: UserContext): Gen[TlaEx] = sized { size =>
    if (size <= 1) {
      exGen(ctx)
    } else {
      for {
        ndefs <- choose(1, maxDefsPerLetIn)
        defs <- listOfN(ndefs, resize(size - 1, genTlaOperDecl(exGen)(ctx))) suchThat { ds =>
          // no new name is present in the context
          ds.map(_.name).toSet.intersect(ctx.map(_.name).toSet).isEmpty &&
          // and all new names are mutually unique
          ds.map(_.name).toSet.size == ds.size
        }
        body <- resize(size - 1, exGen(ctx ++ defs.map(d => UserOperSig(d.name, d.formalParams.length))))
        tt <- genTypeTag
      } yield LetInEx(body, defs: _*).withTag(tt)
    }
  }

  /**
   * Generate a TLA expression.
   *
   * @param builtInOpers a sequence of built-in operators to use.
   * @param ctx          a context of user-defined operators.
   * @return a generator that produces TLA expression (their height is bounded with `sized` and `resize`).
   */
  def genTlaEx(builtInOpers: Seq[TlaOper])(ctx: UserContext): Gen[TlaEx] = lzy {
    sized { size =>
      if (size <= 1) {
        // no gas to generate one more operator expression
        oneOf(genValEx, genNameEx)
      } else {
        for {
          operNo <- choose(0, builtInOpers.length - 1)
          argGen = resize(size - 1, genTlaEx(builtInOpers)(ctx))
          oper = builtInOpers(operNo)
          args <- argsByArity(argGen)(oper.arity)
          tt <- genTypeTag
          result <-
            if (ctx.nonEmpty) {
              // a value, a name,
              // an application of a user-defined operator in the context, an application of a built-in operator
              oneOf(genValEx, genNameEx, genOperApply(genTlaEx(builtInOpers))(ctx),
                  genLetInEx(genTlaEx(builtInOpers))(ctx), const(OperEx(oper, args: _*).withTag(tt)))
            } else {
              // as above but no user-defined operators
              oneOf(genValEx, genNameEx, genLetInEx(genTlaEx(builtInOpers))(ctx),
                  const(OperEx(oper, args: _*).withTag(tt)))
            }
        } yield result
      }
    }
  }

  /**
   * Generate an operator declaration.
   *
   * @param exGen a generator of TLA expressions
   * @param ctx   a context of user-defined operators
   * @return a generator of operator declarations
   */
  def genTlaOperDecl(exGen: UserContext => Gen[TlaEx])(ctx: UserContext): Gen[TlaOperDecl] = {
    for {
      name <- identifier
      body <- exGen(ctx)
      nparams <- choose(0, maxArgs)
      params <- listOfN(nparams, identifier)
      tt <- genTypeTag
    } yield TlaOperDecl(name, params map (n => OperParam(n)), body).withTag(tt)
  }

  /**
   * Generate an assumption.
   *
   * @param exGen a generator of TLA expressions
   * @return a generator of assumptions
   */
  def genTlaAssumeDecl(exGen: Gen[TlaEx]): Gen[TlaAssumeDecl] = {
    for {
      ex <- exGen
      tt <- genTypeTag
    } yield TlaAssumeDecl(ex).withTag(tt)
  }

  /**
   * Generate a constant declaration.
   *
   * @param ctx a context of user declarations.
   * @return a generator of constant declarations
   */
  def genTlaConstDecl(ctx: UserContext): Gen[TlaConstDecl] = {
    for {
      name <- identifier suchThat (n => ctx.forall(d => d.name != n))
      tt <- genTypeTag
    } yield TlaConstDecl(name).withTag(tt)
  }

  /**
   * Generate a variable declaration.
   *
   * @param ctx a context of user declarations.
   * @return a generator of constant declarations
   */
  def genTlaVarDecl(ctx: UserContext): Gen[TlaVarDecl] = {
    for {
      name <- identifier suchThat (n => ctx.forall(d => d.name != n))
      tt <- genTypeTag
    } yield TlaVarDecl(name).withTag(tt)
  }

  /**
   * Generate a declaration of: a constant, a variable, an operator definition, an assumption.
   *
   * @param ctx a context of user declarations.
   * @return a generator of constant declarations
   */
  def genTlaDecl(exGen: UserContext => Gen[TlaEx])(ctx: UserContext): Gen[TlaDecl] = {
    for {
      name <- identifier
      decl <- oneOf(const(TlaConstDecl(name)), const(TlaVarDecl(name)), genTlaAssumeDecl(exGen(ctx)),
          genTlaOperDecl(exGen)(ctx))
    } yield decl
  }

  /**
   * Generate a module
   *
   * @param exGen a generator of TLA expressions
   * @return a generator of modules
   */
  def genTlaModule(exGen: UserContext => Gen[TlaEx]): Gen[TlaModule] = {
    for {
      name <- identifier
      ndecls <- choose(1, maxDeclsPerModule)
      decls <- listOfN(ndecls, genTlaDecl(exGen)(Seq.empty)) suchThat { lst =>
        val defs = lst.collect { case d: TlaOperDecl => d }
        // find the names of the definitions inside the bodies of the global definitions
        val internal = defs.foldLeft(Set.empty[String]) { (set, d) =>
          set ++ internalDefs(d.body)
        }
        // and the name of the global definitions
        val global = defs.foldLeft(Set.empty[String]) { (set, d) =>
          set + d.name
        }
        global.intersect(internal).isEmpty
      }
    } yield new TlaModule(name, decls)
  }

  // compute the set of names that are declared in an expression
  private def internalDefs: TlaEx => Set[String] = {
    case LetInEx(body, defs @ _*) =>
      defs.foldLeft(internalDefs(body)) { (names, d) =>
        names + d.name
      }

    case OperEx(_, args @ _*) =>
      args.foldLeft(Set.empty[String]) { (names, arg) =>
        internalDefs(arg) ++ names
      }

    case _ =>
      Set.empty[String]
  }

  // Given operator arity and an element generator, produce a list of arguments
  private def argsByArity(argGen: Gen[TlaEx]): OperArity => Gen[Seq[TlaEx]] = {
    case AnyArity() => listOf(argGen)

    case FixedArity(n) => listOfN(n, argGen)

    case arity =>
      for {
        sz <- choose(0, maxArgs) suchThat arity.cond
        lst <- listOfN(sz, argGen)
      } yield lst
  }
}
