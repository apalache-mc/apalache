package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.TypingInputException

/**
 * A substitution from constant names to types. It is very similar to Substitution. However, [[TypeAliasSubstitution]]
 * is meant to replace constant types, e.g., ENTRY or \$entryInCamlCase, with a concrete type, whereas [[Substitution]]
 * replaces variables. We use [[TypeAliasSubstitution]] to rewrite type aliases.
 *
 * @param context
 *   a mapping from constant names to types.
 */
class TypeAliasSubstitution(val context: Map[String, TlaType1]) {
  // we put an upper bound on the number of iterations in the closure computation, in case of cyclic dependencies
  private val CLOSURE_LIMIT = 100

  def apply(tp: TlaType1): (TlaType1, Boolean) = {
    TypeAliasSubstitution.mk(context)(tp)
  }

  /**
   * Recursively apply type aliases to all other type aliases in [[context]].
   *
   * @throws TypingInputException
   *   if undefined type aliases are found.
   * @return
   *   a new substitution that has all aliases substituted.
   */
  def closure(): TypeAliasSubstitution = {
    var aliases = context
    // compute a fixpoint by replacing references to aliases with their definitions
    var tries = CLOSURE_LIMIT
    while (tries > 0) {
      val sub = TypeAliasSubstitution(aliases)
      val (newPairs, newChanged) =
        aliases.foldLeft((Seq[(String, TlaType1)](), false)) {
          case ((pairs: Seq[(String, TlaType1)], changed), (key, tt)) =>
            val (newType, newChanged) = sub(tt)
            (pairs :+ (key, newType), newChanged || changed)
        }

      if (newChanged) {
        tries -= 1
      } else {
        tries = 0
      }
      aliases = Map(newPairs: _*)
    }

    // Make sure that all aliases have been substituted.
    // This is basically a postcondition to the above loop to make sure that:
    //  - We have implemented it correctly, and
    //  - There are no cyclic dependencies in the aliases.
    for ((caller, tt) <- aliases) {
      def callback(callee: String) = {
        val msg = s"Cannot resolve a reference to type alias $callee in the type alias $caller. A cyclic dependency?"
        throw new TypingException(msg, UID.nullId)
      }

      throwOnUndefined(aliases.keySet, callback, tt)
    }

    TypeAliasSubstitution(aliases)
  }

  override def toString: String = {
    "ConstSub{%s}".format(String.join(", ", context.toSeq.map(p => "%s -> %s".format(p._1, p._2)): _*))
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[TypeAliasSubstitution]

  override def equals(other: Any): Boolean = other match {
    case that: TypeAliasSubstitution =>
      (that.canEqual(this)) &&
      context == that.context
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(context)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }

  // Make sure that no ConstT1(name) has name in keys. If there is such a name, call the callback.
  private def throwOnUndefined(keys: Set[String], callback: String => Unit, tt: TlaType1): Unit = {
    def search: TlaType1 => Unit = {
      case ConstT1(name) =>
        if (keys.contains(name)) {
          callback(name)
        }

      case SetT1(elem) =>
        search(elem)

      case SeqT1(elem) =>
        search(elem)

      case TupT1(elems @ _*) =>
        elems.foreach(search)

      case SparseTupT1(fieldTypes) =>
        fieldTypes.foreach(p => search(p._2))

      case RecT1(fieldTypes) =>
        fieldTypes.foreach(p => search(p._2))

      case FunT1(arg, res) =>
        search(arg)
        search(res)

      case OperT1(args, res) =>
        search(res)
        args.foreach(search)

      case _ =>
        ()
    }

    search(tt)
  }
}

object TypeAliasSubstitution {
  val empty = new TypeAliasSubstitution(Map.empty)

  def apply(context: Map[String, TlaType1]): TypeAliasSubstitution = {
    new TypeAliasSubstitution(context)
  }

  def mk(fun: PartialFunction[String, TlaType1]): TlaType1 => (TlaType1, Boolean) = {
    def foldWithChanged[T](elems: Seq[T], fun: T => (T, Boolean)): (Seq[T], Boolean) = {
      elems.foldLeft((Seq[T](), false)) { case ((lst, changed), elem) =>
        val (et, echanged) = fun(elem)
        (lst :+ et, changed || echanged)
      }
    }

    def recFun(tp: TlaType1): (TlaType1, Boolean) = {
      tp match {
        case ConstT1(name) =>
          if (fun.isDefinedAt(name)) {
            (fun(name), true)
          } else {
            if (!ConstT1.isAliasReference(name)) {
              // The behavior for an OLD_TYPE_ALIAS is to interpret it as an uninterpreted type,
              // when the user has not written @typeAlias: OLD_TYPE_ALIAS = ...;
              // Hence, in this case we simply do not do any substitution.
              // When we switch to the new aliases completely, this behavior will be forbidden.
              (tp, false)
            } else {
              // with the new alias syntax, we can issue an error
              val originalName = ConstT1.aliasNameFromReference(name)
              val msg = s"Missing @typeAlias: $originalName = <type>;"
              throw new TypingInputException(msg, UID.nullId)
            }
          }

        case VarT1(_) | IntT1 | BoolT1 | RealT1 | StrT1 =>
          (tp, false)

        case SetT1(elem) =>
          val (et, changed) = recFun(elem)
          (SetT1(et), changed)

        case SeqT1(elem) =>
          val (et, changed) = recFun(elem)
          (SeqT1(et), changed)

        case TupT1(elems @ _*) =>
          val (newElems, changed) = foldWithChanged(elems, recFun)
          (TupT1(newElems: _*), changed)

        case SparseTupT1(fieldTypes) =>
          def changePair: (Int, TlaType1) => ((Int, TlaType1), Boolean) = { case (key, tt) =>
            val (ntt, changed) = recFun(tt)
            ((key, ntt), changed)
          }

          val (newPairs, changed) = foldWithChanged(fieldTypes.toSeq, changePair.tupled(_))
          (SparseTupT1(newPairs: _*), changed)

        case RecT1(fieldTypes) =>
          def changePair: (String, TlaType1) => ((String, TlaType1), Boolean) = { case (key, tt) =>
            val (ntt, changed) = recFun(tt)
            ((key, ntt), changed)
          }

          val (newPairs, changed) = foldWithChanged(fieldTypes.toSeq, changePair.tupled(_))
          (RecT1(newPairs: _*), changed)

        case FunT1(arg, res) =>
          val (at, achanged) = recFun(arg)
          val (rt, rchanged) = recFun(res)
          (FunT1(at, rt), achanged || rchanged)

        case OperT1(args, res) =>
          val (newArgs, achanged) = foldWithChanged(args, recFun)
          val (newRes, rchanged) = recFun(res)
          (OperT1(newArgs, newRes), achanged || rchanged)

        case RowT1(fieldTypes, other) =>
          val (ntypes, isChangedFields) = fieldTypes.values.toSeq.map(recFun).unzip
          val nfieldTypes = fieldTypes.keys.zip(ntypes).toSeq
          val hasChangedField = isChangedFields.contains(true)
          other match {
            case None =>
              (RowT1(nfieldTypes: _*), hasChangedField)

            case Some(v) =>
              val (subv, isChangedVar) = recFun(v)
              // nv is either a variable or a row
              subv match {
                case nv @ VarT1(_) =>
                  (RowT1(nv, nfieldTypes: _*), isChangedVar || hasChangedField)

                case RowT1(otherFieldTypes, otherVar) =>
                  (RowT1(otherFieldTypes ++ nfieldTypes, otherVar), isChangedVar || hasChangedField)

                case tp =>
                  throw new IllegalStateException("Expected a var or a row, found: " + tp)
              }
          }

        case RecRowT1(row) =>
          val (newRow, rowChanged) = recFun(row)
          newRow match {
            case r @ RowT1(_, _) =>
              (RecRowT1(r), rowChanged)

            case tt =>
              throw new IllegalStateException("Expected a row after substitution, found: " + tt)
          }

        case VariantT1(row) =>
          val (newRow, rowChanged) = recFun(row)
          newRow match {
            case r @ RowT1(_, _) =>
              (VariantT1(r), rowChanged)

            case tt =>
              throw new IllegalStateException("Expected a row after substitution, found: " + tt)
          }
      }
    }

    recFun
  }

}
