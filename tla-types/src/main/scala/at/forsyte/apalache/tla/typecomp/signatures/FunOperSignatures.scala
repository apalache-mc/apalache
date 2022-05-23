package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{FunT1, SetT1, TupT1}
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap, TypeComputationResult}

/**
 * Produces a SignatureMap for all function/record/tuple operators
 *
 * @author
 *   Jure Kukovec
 */
object FunOperSignatures {

  import TlaFunOper._
  import BuilderUtil._

  def getMap: SignatureMap = {

    // enum does NOT have a signature (the return type depends on the field value)

    // (t1, ..., tn) => <<t1, ..., tn>>
    val tupleSig = signatureMapEntry(tuple, { seq => TupT1(seq: _*) })

    // We only handle function and sequence application through signatures, record/tuple except types depend on key values
    // (a -> b, a) => b
    // or
    // (Seq(a), Int) => a
//    val appSig = signatureMapEntry(app, { case Seq(FunT1(domT, cdmT), t) if t == domT => cdmT })

    // We only handle function and sequence domain through signatures, record/tuple except types depend on key values
    // (a -> b) => Set(a)
    // or
    // (Seq(a)) => Set(Int)
//    val domainSig = signatureMapEntry(domain, { case Seq(FunT1(t, _)) => SetT1(t) })

    // We only need the ternary signature, because the builder interface constructs
    // [x1 \in S1, ..., xn \in Sn |-> e] as [<<x1, ..., xn>> \in S1 \X .. \X Sn |-> e]
    // (t1, t2, Set(t2)) => t1 -> t2
    val funDefSig = signatureMapEntry(funDef, { case Seq(t1, t2, SetT1(tt)) if t2 == tt => FunT1(t1, t2) })

    // We only handle function and sequence  except through signatures, record/tuple except types depend on key values
    // The base case is 1 argument, depth 1, all other except constructors are hybrid.
    // (a -> b, a, b) => a -> b
//    val exceptFunSig = signatureMapEntry(except, { case Seq(funT @ FunT1(a, b), aa, bb) if a == aa && b == bb => funT })

    Map(
        tupleSig,
//        appSig,
//        domainSig,
        funDefSig,
//        exceptFunSig,
    )

  }

}
