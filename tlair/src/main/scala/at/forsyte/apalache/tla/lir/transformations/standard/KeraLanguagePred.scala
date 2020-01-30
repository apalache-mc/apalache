package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSeqOper, _}
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.transformations.LanguagePred
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import scala.collection.immutable.{HashMap, HashSet}

/**
  * <p>Test whether the expressions fit into the flat fragment: all calls to user operators are inlined,
  * except the calls to nullary let-in definitions.</p>
  *
  * <p>To get a better idea of the accepted fragment, check TestKeraLanguagePred.</p>
  *
  * @see TestKeraLanguagePred
  * @author Igor Konnov
  */
class KeraLanguagePred extends LanguagePred {
  override def isModuleOk(mod: TlaModule): Boolean = {
    mod.operDeclarations.forall(d => isExprOk(d.body))
  }

  override def isExprOk(expr: TlaEx): Boolean = {
    isOkInContext(Set(), expr)
  }

  private def isOkInContext(letDefs: Set[String], expr: TlaEx): Boolean = {
    expr match {
      case ValEx(TlaBool(_)) | ValEx(TlaInt(_)) | ValEx(TlaStr(_)) => true
      case ValEx(TlaIntSet) | ValEx(TlaNatSet) | ValEx(TlaBoolSet) => true
      case NameEx(_) => true

      case OperEx(oper, arg) if KeraLanguagePred.unaryOps.contains(oper) =>
        isOkInContext(letDefs, arg)

      case OperEx(BmcOper.withType, lhs, _) =>
        // do not recurse in the type annotation, as it is using special syntax
        isOkInContext(letDefs, lhs)

      case OperEx(oper, lhs, rhs) if KeraLanguagePred.binaryOps.contains(oper) =>
        isOkInContext(letDefs, lhs) && isOkInContext(letDefs, rhs)

      case OperEx(oper, args@_*) if KeraLanguagePred.naryOps.contains(oper) =>
        args forall {
          isOkInContext(letDefs, _)
        }

      case OperEx(oper, NameEx(_), set, pred)
          if KeraLanguagePred.bindingOps.contains(oper) =>
        isOkInContext(letDefs, set) && isOkInContext(letDefs, pred)

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        isOkInContext(letDefs, pred) &&
          isOkInContext(letDefs, thenEx) && isOkInContext(letDefs, elseEx)

      case OperEx(oper, args@_*)
        if oper == TlaSetOper.map || oper == TlaFunOper.funDef =>
        val evenArgs = args.zipWithIndex.filter { p => p._2 % 2 == 0 } map { _._1 }
        evenArgs forall {
          isOkInContext(letDefs, _)
        }

      case LetInEx(body, defs@_*) =>
        // go inside the let definitions
        def eachDefRec(ctx: Set[String], ds: Seq[TlaOperDecl]): Boolean = {
          if (ds.nonEmpty) {
            // check the declaration body first
            if (isOkInContext(ctx, ds.head.body)) {
              // then save that the let definition is ok and continue
              eachDefRec(ctx + ds.head.name, ds.tail)
            } else {
              false
            }
          } else {
            true
          }
        }

        if (!eachDefRec(letDefs, defs)) {
          false
        } else {
          val newLetDefs = defs.map(_.name).toSet
          isOkInContext(letDefs ++ newLetDefs, body)
        }

      case OperEx(TlaOper.apply, NameEx(opName), args@_*) =>
        // the only allowed case is calling a nullary operator that was declared with let-in
        args.isEmpty && letDefs.contains(opName)

      case _ => false
    }
  }
}

object KeraLanguagePred {
  private val singleton = new KeraLanguagePred

  protected val unaryOps: HashSet[TlaOper] =
    HashSet(
      TlaActionOper.prime,
      TlaBoolOper.not,
      TlaArithOper.uminus,
      TlaSetOper.union,
      TlaSetOper.powerset,
      TlaFunOper.domain,
      TlaFiniteSetOper.isFiniteSet,
      TlaFiniteSetOper.cardinality,
      TlaSeqOper.head,
      TlaSeqOper.tail,
      TlaSeqOper.len,
      TlcOper.printT, // TODO: preprocess into NullEx in Keramelizer
      BmcOper.skolemExists,
      BmcOper.expand
      // for the future
      //    TlaActionOper.enabled,
      //    TlaActionOper.unchanged,
      //    TlaTempOper.box,
      //    TlaTempOper.diamond
    ) ////

  protected val binaryOps: HashSet[TlaOper] =
    HashSet(
      TlaOper.eq,
      TlaFunOper.app,
      TlaSetOper.funSet,
      TlaSeqOper.append,
      TlaArithOper.plus,
      TlaArithOper.minus,
      TlaArithOper.mult,
      TlaArithOper.div,
      TlaArithOper.mod,
      TlaArithOper.exp,
      TlaArithOper.dotdot,
      TlaArithOper.lt,
      TlaArithOper.gt,
      TlaArithOper.le,
      TlaArithOper.ge,
      TlaSetOper.in,
      TlaSetOper.cup,
      TlaSetOper.subseteq,
      TlaSeqOper.concat,
      TlcOper.atat,
      TlcOper.colonGreater,
      TlcOper.print, // TODO: preprocess into NullEx in Keramelizer
      TlcOper.assert,
      TlcOper.colonGreater,
      TlcOper.atat,
      BmcOper.withType,
      BmcOper.assign
      // for the future
      //      TlaActionOper.composition,
      //      TlaTempOper.leadsTo,
      //      TlaTempOper.guarantees,
    ) ////


  protected val naryOps: HashSet[TlaOper] =
    HashSet(
      TlaBoolOper.and,
      TlaBoolOper.or,
      TlaSetOper.enumSet,
      TlaFunOper.except,
      TlaFunOper.tuple,
      TlaFunOper.enum,
      TlaSeqOper.subseq,
      TlaOper.label
    ) /////

  protected val bindingOps: HashSet[TlaOper] =
    HashSet(
      TlaBoolOper.exists,
      TlaBoolOper.forall,
      TlaOper.chooseBounded,
      TlaSetOper.filter
    ) /////


  def apply(): KeraLanguagePred = singleton
}