package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, NullEx, OperT1, RealT1, RecT1, SeqT1, SetT1, SparseTupT1, StrT1, TlaType1, TupT1,
  TypingException, UID, VarT1
}

/**
 * A substitution from constant names to types. It is very similar to Substitution. However, `ConstSubstitution` is meant
 * to replace constant types, e.g., ENTRY, with a concrete type, whereas `Substitution` replaces variables.
 * We use `ConstSubstitution` to implement aliases.
 *
 * @param context a mapping from constant names to types.
 */
class ConstSubstitution(val context: Map[String, TlaType1]) {
  // we put an upper bound on the number of iterations in the closure computation, in case of cyclic dependencies
  private val CLOSURE_LIMIT = 100

  def apply(tp: TlaType1): (TlaType1, Boolean) = {
    ConstSubstitution.mk(context)(tp)
  }

  def closure(): ConstSubstitution = {
    var aliases = context
    // compute a fixpoint by replacing references to aliases with their definitions
    var tries = CLOSURE_LIMIT
    while (tries > 0) {
      val sub = ConstSubstitution(aliases)
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

    // make sure that all aliases have been substituted
    for ((caller, tt) <- aliases) {
      def callback(callee: String) = {
        val msg = s"Cannot resolve a reference to type alias $callee in the type alias $caller. A cyclic dependency?"
        throw new TypingException(msg, UID.nullId)
      }

      throwOnUndefined(aliases.keySet, callback, tt)
    }

    ConstSubstitution(aliases)
  }

  override def toString: String = {
    "ConstSub{%s}".format(String.join(", ", context.toSeq.map(p => "%s -> %s".format(p._1, p._2)): _*))
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[ConstSubstitution]

  override def equals(other: Any): Boolean = other match {
    case that: ConstSubstitution =>
      (that canEqual this) &&
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
        elems foreach search

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

object ConstSubstitution {
  val empty = new ConstSubstitution(Map.empty)

  def apply(context: Map[String, TlaType1]): ConstSubstitution = {
    new ConstSubstitution(context)
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
            (tp, false)
          }

        case VarT1(_) | IntT1() | BoolT1() | RealT1() | StrT1() =>
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
      }
    }

    recFun
  }

}
