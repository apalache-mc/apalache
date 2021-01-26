package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.aux.{ExceptionOrValue, FailWith, SucceedWith}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.lir.transformations.standard.{
  IncrementalRenaming,
  InlinerOfUserOper,
  ReplaceFixed
}
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TlaModuleTransformation,
  TransformationTracker
}
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
  * Replaces definitions of user-defined recursive operators with a bounded chain of the operator bodies.
  *
  * For each recursive operator A the user must define two additional TLA+ operators,
  *  - [UNROLL_TIMES_PREFIX]_A
  *  - [UNROLL_DEFAULT_PREFIX]_A
  *
  * Let U be the name of the operator produced by unrolling A with the above parameters.
  * The operator [UNROLL_TIMES_PREFIX]_A must evaluate to an integer `k` (with `ConstSimplifier`) and represents the
  * depth of the unrolling. If the computation of A, for a given argument `x`, requires k or fewer recursive calls, then
  * the value of U(x) is equal to A(x).
  * The operator [UNROLL_DEFAULT_PREFIX]_A must have the same type as that returned by A. If the computation of A,
  * for a given argument `x`, requires more than k recursive calls,
  * then the value of U(x) is equal to [UNROLL_DEFAULT_PREFIX]_A.
  *
  * Example:
  * Fact(n) == IF n <= 0 THEN 1 ELSE n * Fact(n-1)
  * UNROLL_TIMES_Fact == 1
  * UNROLL_DEFAULT_Fact == 0
  *
  *    |
  *    |
  *    V
  *
  * Unrolled_Fact(n) ==
  *  IF n <= 0
  *  THEN 1
  *  ELSE n * (
  *    IF n-1 <= 0
  *    THEN 1
  *    ELSE (n-1) * 0
  *    )
  *
  * Unrolled_Fact(0) = 1, Unrolled_Fact(1) = 1, but for k > 1 Unrolled_Fact(k) = 0
  */
class Unroller(
    nameGenerator: UniqueNameGenerator,
    tracker: TransformationTracker,
    renaming: IncrementalRenaming
) extends TlaModuleTransformation {

  import Unroller._

  // unrollLetIn performs unrolling on all recursive LET-IN defined operators in the expression
  private def unrollLetIn(
      bodyMap: BodyMap
  ): TlaExTransformation = tracker.trackEx {
    case ex @ LetInEx(body, defs @ _*) =>
      val newMap = BodyMapFactory.makeFromDecls(defs, bodyMap)
      val defaultsMap = getDefaults(newMap).getOrThrow
      val replaceTr = replaceWithDefaults(defaultsMap)
      val inliner = InlinerOfUserOper(newMap, tracker)
      // since unrolling preserves operator names, the only thing we need to do at this point is recursively unroll
      // all the LET-definitions
      val newDefs = defs map {
        replaceRecursiveDecl(_, newMap, inliner, replaceTr)
          .asInstanceOf[TlaOperDecl]
      }

      // Since the body may contain more LET-expressions we call unrollLetIn again
      val newBody = unrollLetIn(newMap)(body)
      if (defs == newDefs && body == newBody)
        ex
      else
        LetInEx(newBody, newDefs: _*)
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map unrollLetIn(bodyMap)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)
    case ex => ex
  }

  /**
    * Replaces all instances of operator application, for which a default body exists in `defaultsMap`
    * with the default value.
    */
  private def replaceWithDefaults(
      defaultsMap: Map[String, TlaEx]
  ): TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(TlaOper.apply, NameEx(name), _*)
        if defaultsMap.contains(name) =>
      // Get the default body, ignore the args
      defaultsMap(name)
    // recursive processing of composite operators and let-in definitions
    case ex @ LetInEx(body, defs @ _*) =>
      // transform bodies of all op.defs
      val transform = replaceWithDefaults(defaultsMap)
      val newDefs = defs.map { x =>
        x.copy(body = transform(x.body))
      }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex
      else LetInEx(newBody, newDefs: _*)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map replaceWithDefaults(defaultsMap)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }

  /** Given an operator name, A, extracts the value of [UNROLL_TIMES_PREFIX]_A or throws a `TlaInputError` */
  private def getUnrollLimit(
      name: String,
      bodyMap: BodyMap
  ): ExceptionOrValue[BigInt] = {
    // We get the unrolling limit, which should be an operator in bodyMap.
    // note that operators inside named instances have a qualified name, e.g., I!Foo. Replace "!" with "_".
    val unrollLimitOperName = s"$UNROLL_TIMES_PREFIX$name".replace('!', '_')
    bodyMap.get(unrollLimitOperName) match {
      case Some(unrollLimitDecl) =>
        // The unrollLimit operator must not be recursive ...
        if (unrollLimitDecl.isRecursive) {
          val msg =
            s"Expected an integer bound in $unrollLimitOperName, found a recursive operator. See: $MANUAL_LINK"
          FailWith(new TlaInputError(msg))
        } else {
          // ... and must evaluate to a single integer
          ConstSimplifier(tracker)(
            InlinerOfUserOper(bodyMap, tracker)(unrollLimitDecl.body)
          ) match {
            case ValEx(TlaInt(n)) =>
              SucceedWith(n)
            case e =>
              FailWith(
                new TlaInputError(
                  s"Expected an integer bound in $unrollLimitOperName, found: $e"
                )
              )
          }
        }

      case None =>
        val msg =
          s"Recursive operator $name requires an annotation $unrollLimitOperName. See: $MANUAL_LINK"
        FailWith(new TlaInputError(msg))
    }
  }

  /** Given an operator name, A, extracts the value of [UNROLL_DEFAULT_PREFIX]_A or propmts a `TlaInputError` */
  private def getDefaultBody(
      name: String,
      bodyMap: BodyMap
  ): ExceptionOrValue[TlaEx] = {
    // note that operators inside named instances have a qualified name, e.g., I!Foo. Replace "!" with "_".
    val defaultOperName = s"$UNROLL_DEFAULT_PREFIX$name".replace('!', '_')
    bodyMap.get(defaultOperName) match {
      case Some(defaultDecl) =>
        // ... which must not be recursive ...
        if (defaultDecl.isRecursive) {
          val msg =
            s"Expected a default value in $defaultOperName, found a recursive operator. See: $MANUAL_LINK"
          FailWith(new TlaInputError(msg))
        } else {
          // ... but may be defined using other operators, so we call transform on it
          SucceedWith(InlinerOfUserOper(bodyMap, tracker)(defaultDecl.body))
        }

      case None =>
        FailWith(
          new TlaInputError(
            s"Recursive operator $name requires an annotation $defaultOperName. See: $MANUAL_LINK "
          )
        )
    }
  }

  /** Performs unrolling on the declaration and all recursively defined LET-IN declarations within */
  private def replaceRecursiveDecl(
      decl: TlaDecl,
      bodyMap: BodyMap,
      inliner: InlinerOfUserOper,
      replaceWithDefaultsTr: TlaExTransformation
  ): TlaDecl = decl match {
    case d @ TlaOperDecl(name, fparams, body) if d.isRecursive =>
      // Read the unroll limit
      val unrollLimit = getUnrollLimit(name, bodyMap).getOrThrow
      // Defines inlining k-times
      val kStepInline = inliner.kStepInline(unrollLimit, renaming)
      // Unroll all LET-IN definitions afterward
      val unrolledLetIn = unrollLetIn(bodyMap)(body)
      val inlined = kStepInline(unrolledLetIn)
      // Any remaining applications are default-replaced
      val defaultReplaced = replaceWithDefaultsTr(inlined)
      TlaOperDecl(name, fparams, defaultReplaced)
    case d @ TlaOperDecl(name, fparams, body) => // d.isRecursive = false
      // Even though `name` is not recursive, it still may define recursive LET-IN operators inside
      val unrolledLetIn = unrollLetIn(bodyMap)(body)
      if (body == unrolledLetIn) d
      else TlaOperDecl(name, fparams, unrolledLetIn)
    case TlaRecFunDecl(name, arg, dom, body) =>
      // Ignore for now
      decl
    case _ => decl
  }

  /** Prepares a map of default values, obtained from getDefaultBody  */
  private def getDefaults(
      bodyMap: BodyMap
  ): ExceptionOrValue[Map[String, TlaEx]] = {
    val defMap = bodyMap.values withFilter {
      _.isRecursive
    } map { decl =>
      decl.name -> getDefaultBody(decl.name, bodyMap)
    }
    // We need to prepare a single ExceptionOrValue
    // If multiple keys point to a `FailWith`, we take the 1st
    val init: ExceptionOrValue[Map[String, TlaEx]] = SucceedWith(
      Map.empty[String, TlaEx]
    )
    defMap.foldLeft(init) {
      case (SucceedWith(m), (k, SucceedWith(v))) =>
        SucceedWith(m + (k -> v))
      case (fail: FailWith[Map[String, TlaEx]], _) => fail
      case (_, (_, fail: FailWith[TlaEx])) =>
        FailWith[Map[String, TlaEx]](fail.e)
    }
  }

  override def apply(module: TlaModule): TlaModule = {
    // Before unrolling we transform all recursive operators into parameter-normal form
    // This reduces the number of inlining calls when operator arguments aren't primitive
    val parameterNormalizer = ParameterNormalizer(
      nameGenerator,
      tracker,
      ParameterNormalizer.DecisionFn.recursive
    )
    val paramNormModule = parameterNormalizer.normalizeModule(module)

    // Next we prepare the various maps and transformations ...
    val operDecls = paramNormModule.operDeclarations
    val bodyMap = BodyMapFactory.makeFromDecls(operDecls)
    val defaultsMap = getDefaults(bodyMap).getOrThrow
    val replaceTr = replaceWithDefaults(defaultsMap)
    val inliner = InlinerOfUserOper(bodyMap, tracker)
    // ... and unroll all declarations
    val newDecls = paramNormModule.declarations map {
      replaceRecursiveDecl(_, bodyMap, inliner, replaceTr)
    }

    new TlaModule(paramNormModule.name, newDecls)
  }
}

object Unroller {
  val UNROLL_TIMES_PREFIX: String = "UNROLL_TIMES_"
  val UNROLL_DEFAULT_PREFIX: String = "UNROLL_DEFAULT_"
  val MANUAL_LINK: String =
    "https://apalache.informal.systems/docs/apalache/principles.html#recursion"

  def apply(
      nameGenerator: UniqueNameGenerator,
      tracker: TransformationTracker,
      renaming: IncrementalRenaming
  ): Unroller = {
    new Unroller(nameGenerator, tracker, renaming)
  }
}
