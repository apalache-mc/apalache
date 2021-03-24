package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{OperT1, _}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.{DeclarationSorter, ModuleByExTransformer, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import TypedPredefs._
import com.typesafe.scalalogging.LazyLogging

/**
 * A rewriter of definitions and constants that replaces every definition Foo with the definition seen in OVERRIDE_Foo,
 * if OVERRIDE_Foo is present.
 *
 * @author Igor Konnov
 * @author Andrey Kuprianov
 */
class ConstAndDefRewriter(tracker: TransformationTracker) extends TlaModuleTransformation with LazyLogging {
  override def apply(mod: TlaModule): TlaModule = {
    val overrides = findOverrides(mod.operDeclarations)

    def transformDef: TlaDecl => TlaDecl = {
      case d @ TlaConstDecl(name) if overrides.contains(name) =>
        val overridingDef = overrides(name)
        if (overridingDef.formalParams.nonEmpty) {
          val nargs = overridingDef.formalParams.size
          val msg = s"  > Replacing constant $name with an operator body that has $nargs parameters"
          logger.error(msg)
          logger.error("  > If you need support for n-ary CONSTANTS, write a feature request.")
          throw new OverridingError(msg, overridingDef.body)
        } else if (d.typeTag != overridingDef.body.typeTag) {
          val msg = s"The types of ${d.name} and ${overridingDef.name} do not match."
          logger.error(msg)
          throw new OverridingError(msg, overridingDef.body)
        } else {
          logger.info(s"  > Replaced CONSTANT $name with ${overridingDef.body}")
          // Safe constructor: cannot be recursive
          // Instead of a constant, we have an operator now. Use an operator type.
          val typeTag = Typed(OperT1(Seq(), d.typeTag.asTlaType1()))
          TlaOperDecl(name, List(), overridingDef.body)(typeTag)
        }

      case TlaOperDecl(name, dfParams, _) if overrides.contains(name) =>
        val overridingDef = overrides(name)
        if (overridingDef.formalParams.size != dfParams.size) {
          val odNargs = overridingDef.formalParams.size
          val dfNargs = dfParams.size
          val msg =
            s"  > Replacing operator $name ($dfNargs) with an operator ${overridingDef.name} that has $odNargs parameters"
          throw new OverridingError(msg, overridingDef.body)
        } else {
          logger.info(s"  > Replaced operator $name with OVERRIDE_$name")
          // Note: can be overridden with a recursive operator, so we need to preserve .isRecursive
          overridingDef.copy(name = name)
        }

      case df @ TlaVarDecl(name) if overrides.contains(name) =>
        val msg = s"  > Trying to replace variable $name with an operator OVERRIDE_$name. Use INSTANCE ... WITH"
        throw new OverridingError(msg, NullEx)

      case df => df // keep the definition intact
    }

    // substitute the constant definitions and operator definitions with the replacement operators
    val transformed = mod.declarations map transformDef
    val filtered = transformed filter (!_.name.startsWith(ConstAndDefRewriter.OVERRIDE_PREFIX))
    val sortedModule =
      try {
        new DeclarationSorter()(new TlaModule(mod.name, filtered))
      } catch {
        case e: CyclicDependencyError =>
          // re-throw this exception as a configuration error, so the user would see a nice message
          throw new ConfigurationError(e.getMessage)
      }

    // Importantly, for every constant c, replace NameEx(c) with OperEx(TlaOper.apply, replacement).
    // This is needed as we distinguish the operator calls from constant and variable use.

    def replaceConstWithCall(mod: TlaModule, constDecl: TlaConstDecl): TlaModule = {
      val tag = constDecl.typeTag
      val operTag = Typed(OperT1(Seq(), constDecl.typeTag.asTlaType1()))
      val name = constDecl.name
      val xform = ReplaceFixed(tracker)(NameEx(name)(tag), OperEx(TlaOper.apply, NameEx(name)(operTag))(tag))
      val moduleXform = ModuleByExTransformer(xform)
      moduleXform(mod)
    }

    val replacedConsts = mod.declarations.collect { case d @ TlaConstDecl(name) if overrides.contains(name) => d }
    val replaced = replacedConsts.foldLeft(sortedModule)(replaceConstWithCall)
    replaced
  }

  private def findOverrides(defs: Seq[TlaDecl]): Map[String, TlaOperDecl] = {
    val overrides =
      defs.collect {
        case df: TlaOperDecl if df.name.startsWith(ConstAndDefRewriter.OVERRIDE_PREFIX) =>
          df.name.substring(ConstAndDefRewriter.OVERRIDE_PREFIX.length) -> df
      }

    Map(overrides: _*)
  }
}

object ConstAndDefRewriter {
  val OVERRIDE_PREFIX = "OVERRIDE_"
}
