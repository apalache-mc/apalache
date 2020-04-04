package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.{ModuleByExTransformer, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Set

/**
  * A rewriter of definitions and constants that replaces every definition Foo with the definition seen in OVERRIDE_Foo,
  * if OVERRIDE_Foo is present.
  *
  * @author Igor Konnov
  */
class ConstAndDefRewriter(tracker: TransformationTracker) extends TlaModuleTransformation with LazyLogging {
  override def apply(mod: TlaModule): TlaModule = {
    val overrides = findOverrides(mod.operDeclarations)

    def transformDef: TlaDecl => TlaDecl = {
      case TlaConstDecl(name) if overrides.contains(name) =>
        val overridingDef = overrides(name)
        if (overridingDef.formalParams.nonEmpty) {
          val nargs = overridingDef.formalParams.size
          val msg = s"  > Replacing constant $name with an operator body that has $nargs parameters"
          logger.error(msg)
          logger.error("  > If you need support for n-ary CONSTANTS, write a feature request.")
          throw new OverridingError(msg, overridingDef.body)
        } else {
          logger.info(s"  > Replaced CONSTANT $name")
          TlaOperDecl(name, List(), overridingDef.body)
        }

      case df @ TlaOperDecl(name, dfParams, _) if overrides.contains(name) =>
        val overridingDef = overrides(name)
        if (overridingDef.formalParams.size != dfParams.size) {
          val odNargs = overridingDef.formalParams.size
          val dfNargs = dfParams.size
          val msg = s"  > Replacing operator $name ($dfNargs) with an operator ${overridingDef.name} that has $odNargs parameters"
          throw new OverridingError(msg, overridingDef.body)
        } else {
          logger.info(s"  > Replaced operator $name with OVERRIDE_$name")
          TlaOperDecl(name, overridingDef.formalParams, overridingDef.body)
        }

      case df @ TlaVarDecl(name) if overrides.contains(name) =>
        val msg = s"  > Trying to replace variable $name with an operator OVERRIDE_$name. Use INSTANCE ... WITH"
        throw new OverridingError(msg, NullEx)

      case df => df // keep the definition intact
    }

    // substitute the constant definitions and operator definitions with the replacement operators
    val transformed = mod.declarations map transformDef
    val filtered = transformed filter (!_.name.startsWith(ConstAndDefRewriter.OVERRIDE_PREFIX))
    val sorted = toposortDefs(filtered)
    // Importantly, for every constant c, replace NameEx(c) with OperEx(TlaOper.apply, replacement).
    // This is needed as we distinguish the operator calls from constant and variable use.

    def replaceConstWithCall(mod: TlaModule, name: String): TlaModule = {
      val xform = ReplaceFixed(NameEx(name), OperEx(TlaOper.apply, NameEx(name)), tracker)
      val moduleXform = ModuleByExTransformer(xform)
      moduleXform(mod)
    }

    val replacedConsts = mod.declarations.collect { case TlaConstDecl(name) if overrides.contains(name) => name }
    val replaced = replacedConsts.foldLeft(new TlaModule(mod.name, sorted))(replaceConstWithCall)
    replaced
  }

  private def findOverrides(defs: Seq[TlaDecl]): Map[String, TlaOperDecl] = {
    val overrides =
      defs.collect {
        case df: TlaOperDecl if df.name.startsWith(ConstAndDefRewriter.OVERRIDE_PREFIX) =>
          df.name.substring(ConstAndDefRewriter.OVERRIDE_PREFIX.length) -> df
      }

    Map(overrides :_*)
  }

  private def toposortDefs(defs: Seq[TlaDecl]): Seq[TlaDecl] = {

    var defsWithDeps = List[(TlaDecl,Set[String])](
      defs.map {
        case d@TlaOperDecl(_, params, body) =>
          val paramSet = Set[String](params.collect {
            case p => p.name
          }:_*)
          (d, findDeps(body) -- paramSet)
       case d => (d, Set[String]())
      }:_*
    )
    var sorted = ListBuffer[TlaDecl]()
    var added = Set[String]()
    var newAdded = false
    do {
      newAdded = false
      val remain = ListBuffer[(TlaDecl, Set[String])]()
      defsWithDeps.foreach {
        case (d, deps) =>
          val newDeps = deps -- added
          if(newDeps.isEmpty) {
            sorted += d
            added += d.name
            newAdded = true
          }
          else {
            remain += ((d, deps))
          }
          true
      }
      defsWithDeps = remain.toList
    }
    while(!defsWithDeps.isEmpty && newAdded)
    if(!defsWithDeps.isEmpty) {
      logger.error(s"  > toposort remaining definitions: ${defsWithDeps.toString}")
      throw new Exception("Circular input dependency detected" )
    }
    sorted
  }

  private def findDeps(expr: TlaEx): Set[String] = {
    expr match {
      case NameEx(name) => Set(name)
      case  OperEx(op, x, s, p)
        if op == TlaOper.chooseBounded ||  op == TlaBoolOper.exists || op == TlaBoolOper.forall =>
        findDeps(s) ++ findDeps(p) -- List(x.asInstanceOf[NameEx].name)
      case  OperEx(op, x, p)
        if op == TlaOper.chooseUnbounded ||  op == TlaBoolOper.existsUnbounded || op == TlaBoolOper.forallUnbounded =>
        findDeps(p) -- List(x.asInstanceOf[NameEx].name)
      case OperEx(op, body, keysAndValues@_*)
        if op == TlaFunOper.funDef =>
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1.asInstanceOf[NameEx].name), vs.map(_._1))
        findDeps(body) ++ values.foldLeft(Set[String]()){
          case (s, x) => s ++ findDeps(x)
        } -- keys
      case OperEx(_, args@_*) =>
        args.foldLeft(Set[String]()) {
          case (s, e) => s ++ findDeps(e)
        }
      case _ => Set[String]()
    }
  }

}

object ConstAndDefRewriter {
  val OVERRIDE_PREFIX = "OVERRIDE_"
}
