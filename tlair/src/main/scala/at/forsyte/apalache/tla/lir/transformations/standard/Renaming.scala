package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

import scala.collection.immutable.HashMap

/**
  * This class contains methods that are related to renaming.
  *
  * @author Igor Konnov
  *
  * TODO: shall we move this class to *.lir.transformations.standard?
  */
class Renaming (tracker: TransformationTracker) extends TlaExTransformation {
  /**
    * The names of bindings that have been seen already.
    */
  private var seenNames: Map[String, Int] = HashMap[String, Int]()

  override def apply(e: TlaEx): TlaEx = {
    renameBindingsUnique(e)
  }

  def apply( decl : TlaDecl ) : TlaDecl = decl match {
    case TlaOperDecl( name, params, body ) =>
      val paramMap = (params map { p =>
        val pName = p.name
        pName -> assignUniqueName( pName )
      }).toMap

      val retDecl = TlaOperDecl(
        name,
        params map {
          case SimpleFormalParam( p ) => SimpleFormalParam( paramMap( p ) )
          case OperFormalParam( p, a ) => OperFormalParam( paramMap( p ), a )
        },
        rename( paramMap )( body )
      )

      retDecl
    case _ => decl
  }

  private def assignUniqueName(name: String): String = {
    val newVersion = 1 + seenNames.getOrElse(name, 0)
    seenNames += name -> newVersion
    // Jure: 30.8.19: changed name + version to name + _ + version, because calling renaming twice
    // can create indistinguishable expressions e.g. p + 11 + 1 and p + 1 + 11
    s"${name}_$newVersion" // assign a unique name, e.g., x1, x2, x3, etc.
  }

  private def rename(map: Map[String, String]): TlaExTransformation = tracker.track {
    case ex @ NameEx(name) =>
      if (map.contains(name)) {
        val newEx = NameEx(map(name))
        newEx
      } else {
        ex // nothing changes, so no new id is assigned
      }

    case LetInEx( body, defs@_* ) =>
      val opersAndFParamsNameMap = ( defs flatMap {
        case TlaOperDecl( n, params, _ ) => ( n -> assignUniqueName( n ) ) +: (
          params map { p =>
            val pName = p.name
            pName -> assignUniqueName( pName )
          } )
      } ).toMap

      val newMap = map ++ opersAndFParamsNameMap

      val newDefs = defs map {
        case TlaOperDecl( n, ps, b ) =>
          TlaOperDecl(
            opersAndFParamsNameMap( n ),
            ps map {
              case SimpleFormalParam( p ) => SimpleFormalParam( opersAndFParamsNameMap( p ) )
              case OperFormalParam( p, a ) => OperFormalParam( opersAndFParamsNameMap( p ), a )
            },
            rename( newMap )( b )
          )
      }
      val newBody = rename( newMap )( body )
      LetInEx( newBody, newDefs : _* )

    case OperEx(op, NameEx(name), otherArgs@_*)
      if op == TlaSetOper.filter
        || op == TlaBoolOper.exists || op == TlaBoolOper.forall
        || op == TlaOper.chooseBounded || op == TlaOper.chooseUnbounded
        || op == TlaOper.chooseIdiom =>

      val newName = assignUniqueName(name)
      val newMap = map + (name -> newName)
      val newArgs = otherArgs.map(e => rename(newMap)(e))
      OperEx(op, NameEx(newName) +: newArgs: _*)

    case OperEx(op, result, varsAndSets@_*)
      if op == TlaSetOper.map || op == TlaFunOper.funDef =>
      val names = varsAndSets.zipWithIndex.collect { case (e @ NameEx(_), i) if i % 2 == 0 => e }
      val sets = varsAndSets.zipWithIndex.collect { case (e, i) if i % 2 == 1 => e }

      assert(names.length + sets.length == varsAndSets.length)

      def each(m: Map[String, String], n: String): Map[String, String] = {
        m + (n -> assignUniqueName(n))
      }

      val newMap = names.map(_.name).foldLeft(map)(each)
      def introName(ne: NameEx): NameEx = {
        if (!newMap.contains(ne.name)) {
          ne // keep the old expression, as it does not change the link to the source code
        } else {
          NameEx(newMap(ne.name))
        }
      }
      val newNames = names map introName
      val newSets = sets.map(e => rename(newMap)(e))
      val newResult = rename(newMap)(result)

      def fold(s: Seq[TlaEx], p: Tuple2[TlaEx, TlaEx]) = p._1 +: p._2 +: s

      val newArgs = newNames.zip(newSets).foldLeft(Seq[TlaEx]())(fold)
      val newEx = OperEx(op, newResult +: newArgs: _*)
      newEx

    case OperEx(op, args@_*) =>
      val newEx = OperEx(op, args.map(e => rename(map)(e)): _*)
      newEx

    case ex => ex
  }

  /**
    * <p>Rename all bindings so that the bound variable names become unique
    * across all the code. For instance, \E x \in S: x > 1 /\ \E x \in T: x < 2
    * becomes \E x1 \in S: x1 > 1 /\ \E x2 \in T: x2 < 2. This method
    * does not expand operator definitions.</p>
    *
    * <p>WARNING: this method saves the unique names. That is, multiple calls to this method
    * will produce expressions with unique bound variables.</p>
    *
    * @param expr an expression to modify
    * @return an equivalent expression whose bound variables are uniquely renamed
    */
  def renameBindingsUnique(expr: TlaEx): TlaEx = {
    // rename the bound variables
    rename(HashMap())(expr)
  }
}
