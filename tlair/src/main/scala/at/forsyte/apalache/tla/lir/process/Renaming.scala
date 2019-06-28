package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import com.google.inject.Inject
import javax.inject.Singleton

import scala.collection.immutable.{HashMap, HashSet}

/**
  * This class contains methods that are related to renaming.
  *
  * @author Igor Konnov
  */
@Singleton
class Renaming @Inject()(val handler: EnvironmentHandler) {
  /**
    * The names of bindings that have been seen already.
    */
  private var seenNames = HashSet[String]()

  /**
    * <p>Rename all bindings so that the bound variable names become unique
    * across all the code. For instance, \E x \in S: x > 1 /\ \E x \in T: x < 2
    * becomes \E x$1 \in S: x$1 > 1 /\ \E x$2 \in T: x$2 < 2. This method
    * does not expand operator definitions.</p>
    *
    * <p>WARNING: this method saves the unique names. That is, multiple calls to this method
    * will produce expressions with unique bound variables.</p>
    *
    * @param expr an expression to modify
    * @return an equivalent expression whose bound variables are uniquely renamed
    */
  def renameBindingsUnique(expr: TlaEx): TlaEx = {
    def findUniqueName(name: String): String = {
      def find(i: Int): Int = {
        if (!seenNames.contains(name + i)) {
          i
        } else {
          find(i + 1)
        }
      }

      name + find(2)
    }

    def rename(map: Map[String, String], ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        if (map.contains(name)) {
          val newEx = NameEx(map(name))
          handler.m_listener.onTransformation(ex, newEx)
          newEx
        } else {
          ex // nothing changes, so no new id is assigned
        }

      case ValEx(_) => ex

      case OperEx(op, ne @ NameEx(name), otherArgs@_*)
        if op == TlaSetOper.filter
          || op == TlaBoolOper.exists || op == TlaBoolOper.forall
          || op == TlaOper.chooseBounded || op == TlaOper.chooseUnbounded
          || op == TlaOper.chooseIdiom =>
        val newEx =
          if (!seenNames.contains(name)) {
            seenNames += name
            val newArgs = otherArgs.map(rename(map, _))
            OperEx(op, ne +: newArgs: _*)
          } else {
            val newName = findUniqueName(name)
            seenNames += newName
            val newMap = map + (name -> newName)
            val newArgs = otherArgs.map(rename(newMap, _))
            val newNameEx = NameEx(newName)
            handler.m_listener.onTransformation(ne, newNameEx)
            OperEx(op, newNameEx +: newArgs: _*)
          }
        handler.m_listener.onTransformation(ex, newEx)
        newEx

      case OperEx(op, result, varsAndSets@_*)
        if op == TlaSetOper.map || op == TlaFunOper.funDef =>
        val names = varsAndSets.zipWithIndex.collect { case (e @ NameEx(_), i) if i % 2 == 0 => e }
        val sets = varsAndSets.zipWithIndex.collect { case (e, i) if i % 2 == 1 => e }

        assert(names.length + sets.length == varsAndSets.length)

        def each(m: Map[String, String], n: String): Map[String, String] = {
          if (!seenNames.contains(n)) {
            seenNames += n
            m
          } else {
            val newName = findUniqueName(n)
            seenNames += newName
            m + (n -> newName)
          }
        }

        val newMap = names.map(_.name).foldLeft(map)(each)
        def introName(ne: NameEx): NameEx = {
          if (!newMap.contains(ne.name)) {
            ne // keep the old expression, as it does not change the link to the source code
          } else {
            val nne = NameEx(newMap(ne.name))
            handler.m_listener.onTransformation(ne,nne)
            nne
          }
        }
        val newNames = names map introName
        val newSets = sets.map(rename(newMap, _))
        val newResult = rename(newMap, result)

        def fold(s: Seq[TlaEx], p: Tuple2[TlaEx, TlaEx]) = p._1 +: p._2 +: s

        val newArgs = newNames.zip(newSets).foldLeft(Seq[TlaEx]())(fold)
        val newEx = OperEx(op, newResult +: newArgs: _*)
        handler.m_listener.onTransformation(ex, newEx)
        newEx

      case OperEx(op, args@_*) =>
        val newEx = OperEx(op, args.map(e => rename(map, e)): _*)
        handler.m_listener.onTransformation(ex, newEx)
        newEx
    }

    // rename the bound variables
    rename(HashMap(), expr)
  }
}
