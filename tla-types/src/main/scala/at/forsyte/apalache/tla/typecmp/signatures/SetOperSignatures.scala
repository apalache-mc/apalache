package at.forsyte.apalache.tla.typecmp.signatures

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, OperT1, SeqT1, SetT1, TupT1}
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.SignatureGenMap

/**
 * Produces a SignatureMap for all set operators
 *
 * @author
 *   Jure Kukovec
 */
object SetOperSignatures {
  import TlaSetOper._

  /**
   * Returns a map that assigns a signature generator to each TlaSetOper. Because most operators are polymorphic, their
   * signatures will contain type variables produced on-demand by varPool.
   */
  def getMap(varPool: TypeVarPool): SignatureGenMap = {

    // \cup, \cap, \ are binary, polymorphic and symm (w.r.t. arg types)
    // (Set(t), Set(t)) => Set(t)
    val binarySymm: SignatureGenMap = Seq(
        cup,
        cap,
        setminus,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        OperT1(Seq.fill(2)(SetT1(t)), SetT1(t))
      }
    }.toMap

    // \in, \notin are similar, but asymm w.r.t arg types
    // (t, Set(t)) => Bool
    val binaryAsymm: SignatureGenMap = Seq(
        in,
        notin,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        OperT1(Seq(t, SetT1(t)), BoolT1())
      }
    }.toMap

    // map is polyadic, with 2k + 1 args in general
    // (t, t1, Set(t1), ..., tk, Set(tk)) => Set(t)
    val mapSig = map -> { n: Int =>
      val npairs = (n - 1) / 2
      val t = varPool.fresh
      val ts = varPool.fresh(npairs)

      val elemSetParis = ts.flatMap { tt =>
        Seq(tt, SetT1(tt))
      }
      OperT1(t +: elemSetParis, SetT1(t))
    }

    // { x \in S: p } is polymorphic
    // (t, Set(t), Bool) => Set(t)
    val filterSig = filter -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(t, SetT1(t), BoolT1()), SetT1(t))
    }

    // recSet does NOT have a signature (the return type depends on the field value)

    // Seq(S) is polymorphic, fixed arity 1
    // (Set(t)) => Set(Seq(t))
    val seqSetSig = seqSet -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SetT1(t)), SetT1(SeqT1(t)))
    }

    // SUBSET S is polymorphic, fixed arity 1
    // (Set(t)) => Set(Set(t))
    val powSetSig = powerset -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SetT1(t)), SetT1(SetT1(t)))
    }

    // \X is polyadic with n = 2 + k args
    // (Set(t1), ..., Set(tn)) => Set(<<t1,...,tn>>)
    val timesSig = times -> { n: Int =>
      val ts = varPool.fresh(n)
      OperT1(ts.map(SetT1), SetT1(TupT1(ts: _*)))
    }

    // [_ -> _] is polymorphic
    // (Set(t1), Set(t2)) => Set(t1 -> t2)
    val funSetSig = funSet -> { _: Int =>
      val ts @ Seq(domT, cdmT) = varPool.fresh(2)
      OperT1(ts.map(SetT1), SetT1(FunT1(domT, cdmT)))
    }

    // UNION is polymorphic, fixed arity 1
    // (Set(Set(t))) => Set(t)
    val unionSig = union -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SetT1(SetT1(t))), SetT1(t))
    }

    // { _ } is polyadic
    // (t, ..., t) => Set(t)
    val enumSig = enumSet -> { n: Int =>
      val t = varPool.fresh
      OperT1(Seq.fill(n)(t), SetT1(t))
    }

    // \subseteq is polymorphic
    // (t, ..., t) => Set(t)
    val subseteqSig = subseteq -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SetT1(t), SetT1(t)), BoolT1())
    }

    val rest: SignatureGenMap = Seq(
        mapSig,
        filterSig,
        seqSetSig,
        powSetSig,
        timesSig,
        funSetSig,
        unionSig,
        enumSig,
        subseteqSig,
    ).toMap

    binarySymm ++ binaryAsymm ++ rest
  }
}
