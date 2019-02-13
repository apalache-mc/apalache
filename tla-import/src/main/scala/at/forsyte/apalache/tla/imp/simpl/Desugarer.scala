package at.forsyte.apalache.tla.imp.simpl

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import javax.inject.Singleton

/**
  * Remove annoying syntactic sugar. For the moment, we only deal with [f EXCEPT ![i][j]...[k] = ..],
  * but in the future we should move most of the pre-processing code to this class, unless it really changes
  * the expressive power.
  *
  * @author Igor Konnov
  */
@Singleton
class Desugarer {
  def transform(expr: TlaEx): TlaEx = {
    expr match {
      case NameEx(_) | ValEx(_) => expr

      case OperEx(TlaFunOper.except, fun, args @ _*) =>
        val accessors = args.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val newValues = args.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val nonSingletons = accessors.collect { case OperEx(TlaFunOper.tuple, lst @ _*) => lst.size > 1 }
        if (nonSingletons.isEmpty) {
          // only singleton tuples, do nothing
          expr
        } else {
          // multiple accesses, e.g., ![i][j] = ...
          expandExcept(fun, accessors, newValues)
        }

      case OperEx(TlaActionOper.unchanged, tex @ OperEx(TlaFunOper.tuple, args @ _*)) =>
        OperEx(TlaActionOper.unchanged, OperEx(TlaFunOper.tuple, flattenTuples(tex) :_*))

      case OperEx(op, args @ _*) =>
        OperEx(op, args map transform :_*)
    }
  }

  private def flattenTuples(ex: TlaEx): Seq[TlaEx] = ex match {
    case OperEx(TlaFunOper.tuple, args @ _*) =>
      args.map(flattenTuples).reduce(_ ++ _)

    case _ => Seq(ex)
  }

  private def expandExcept(topFun: TlaEx, accessors: Seq[TlaEx], newValues: Seq[TlaEx]): TlaEx = {
    def untuple: PartialFunction[TlaEx, Seq[TlaEx]] = { case OperEx(TlaFunOper.tuple, args @ _*) => args }
    def unfoldKey(indicesInPrefix: Seq[TlaEx], indicesInSuffix: Seq[TlaEx], newValue: TlaEx): TlaEx = {
      // produce [f[i_1]...[i_m] EXCEPT ![i_m+1] = unfoldKey(...) ]
      indicesInSuffix match {
        case Nil => newValue // nothing to unfold, just return g
        case oneMoreIndex +: otherIndices =>
          // f[i_1]...[i_m]
          val funApp = indicesInPrefix.foldLeft(topFun) ((f, i) => tla.appFun(f, i))
          // the recursive call defines another chain of EXCEPTS
          val rhs = unfoldKey(indicesInPrefix :+ oneMoreIndex, otherIndices, newValue)
          OperEx(TlaFunOper.except, funApp, tla.tuple(oneMoreIndex), rhs)
      }
    }

    def eachPair(accessor: TlaEx, newValue: TlaEx): (TlaEx, TlaEx) = {
      val indices = untuple(accessor)
      // ![e_1][e_2]...[e_k] = g becomes ![e_1] = h
      val lhs = tla.tuple(indices.head)
      // h is computed by unfoldKey
      val rhs = unfoldKey(Seq(indices.head), indices.tail, newValue)
      (lhs, rhs)
    }
    val expandedPairs = accessors.zip(newValues) map (eachPair _).tupled
    val expandedArgs = 0.until(2 * expandedPairs.size) map
      (i => if (i % 2 == 0) expandedPairs(i / 2)._1 else expandedPairs(i / 2)._2)
    OperEx(TlaFunOper.except, topFun +: expandedArgs :_*)
  }

}
