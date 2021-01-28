package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{OperEx, ValEx}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaStr

class SignatureGenerator {
  private val typeVarGenerator: TypeVarGenerator = new TypeVarGenerator

  def getPossibleSignatures(operEx: OperEx): List[PolyOperT] =
    operEx.oper match {

      /** Logic */
      case TlaOper.eq | TlaOper.ne =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(t, t), BoolT)))
      case TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.implies |
          TlaBoolOper.equiv =>
        List(
          PolyOperT(
            List.empty,
            OperT(TupT(List.fill(operEx.args.length)(BoolT): _*), BoolT)
          )
        )
      case TlaBoolOper.not =>
        List(PolyOperT(List.empty, OperT(TupT(BoolT), BoolT)))
      case TlaBoolOper.forall | TlaBoolOper.exists =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(t, SetT(t), BoolT), BoolT)))

      /** Choose */
      case TlaOper.chooseBounded =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(t, SetT(t), BoolT), t)))

      /** Arithmetic */
      case TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.mult |
          TlaArithOper.div | TlaArithOper.mod =>
        List(PolyOperT(List.empty, OperT(TupT(IntT, IntT), IntT)))
      case TlaArithOper.uminus =>
        List(PolyOperT(List.empty, OperT(TupT(IntT), IntT)))
      case TlaArithOper.dotdot =>
        List(PolyOperT(List.empty, OperT(TupT(IntT, IntT), SetT(IntT))))
      case TlaArithOper.le | TlaArithOper.lt | TlaArithOper.ge |
          TlaArithOper.gt =>
        List(PolyOperT(List.empty, OperT(TupT(IntT, IntT), BoolT)))

      /** Sets */
      case TlaSetOper.in | TlaSetOper.notin =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(t, SetT(t)), BoolT)))
      case TlaSetOper.supsetProper | TlaSetOper.subsetProper |
          TlaSetOper.supseteq | TlaSetOper.subseteq =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(SetT(t), SetT(t)), BoolT)))
      case TlaSetOper.cup | TlaSetOper.cap | TlaSetOper.setminus =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(SetT(t), SetT(t)), SetT(t))))
      case TlaSetOper.enumSet =>
        val t = typeVarGenerator.getUnique
        List(
          PolyOperT(
            List(t),
            OperT(TupT(List.fill(operEx.args.length)(t): _*), SetT(t))
          )
        )
      case TlaSetOper.filter =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(t, SetT(t), BoolT), SetT(t))))
      case TlaSetOper.map =>
        val n = (operEx.args.length - 1) / 2
        val t = typeVarGenerator.getUnique
        val ts = typeVarGenerator.getNUnique(n)
        val allPairs = ts flatMap { x =>
          List(x, SetT(x))
        }
        List(PolyOperT(t +: ts, OperT(TupT(t +: allPairs: _*), SetT(t))))
      case TlaSetOper.powerset =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(SetT(t)), SetT(SetT(t)))))
      case TlaSetOper.union =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(SetT(SetT(t))), SetT(t))))

      /** Functions */
      case TlaFunOper.domain =>
        val ts = typeVarGenerator.getNUnique(2)
        val List(t1, t2) = ts
        List(PolyOperT(ts, OperT(TupT(FunT(t1, t2)), SetT(t2))))
      case TlaSetOper.funSet =>
        val ts = typeVarGenerator.getNUnique(2)
        val List(t1, t2) = ts
        List(PolyOperT(ts, OperT(TupT(SetT(t1), SetT(t2)), SetT(FunT(t1, t2)))))
      case TlaFunOper.funDef =>
        val n = (operEx.args.length - 1) / 2
        val t = typeVarGenerator.getUnique
        val ts = typeVarGenerator.getNUnique(n)
        val allPairs = ts flatMap { x =>
          List(x, SetT(x))
        }
        List(
          PolyOperT(
            t +: ts,
            OperT(TupT(t +: allPairs: _*), FunT(TupT(ts: _*), t))
          )
        )

      /** Records */
      case TlaSetOper.recSet =>
        val kvPairs = operEx.args.zipWithIndex.collect {
          case (ValEx(TlaStr(s)), i) if i % 2 == 0 =>
            KvPair(s, typeVarGenerator.getUnique)
        }
        val ts = kvPairs map {
          _.v.asInstanceOf[TypeVar]
        }
        val tupArgs = kvPairs flatMap { pa =>
          List(StrT, SetT(pa.v))
        }
        List(
          PolyOperT(
            ts.toList,
            OperT(TupT(tupArgs: _*), SetT(RecT(kvPairs: _*)))
          )
        )

      /** Tuples */
      case TlaFunOper.tuple =>
        val ts = typeVarGenerator.getNUnique(operEx.args.length)
        List(PolyOperT(ts, OperT(TupT(ts: _*), TupT(ts: _*))))
      case TlaSetOper.times =>
        val ts = typeVarGenerator.getNUnique(operEx.args.length)
        List(PolyOperT(ts, OperT(TupT(ts map SetT: _*), SetT(TupT(ts: _*)))))

      /** Control */
      case TlaControlOper.ifThenElse =>
        val t = typeVarGenerator.getUnique
        List(PolyOperT(List(t), OperT(TupT(BoolT, t, t), t)))
      case TlaControlOper.caseNoOther =>
        val n = operEx.args.length / 2
        val t = typeVarGenerator.getUnique
        val tupArgs = for {
          _ <- 1 to n
          v <- List(BoolT, t)
        } yield v

        List(PolyOperT(List(t), OperT(TupT(tupArgs: _*), t)))
      case TlaControlOper.caseWithOther =>
        val n = (operEx.args.length - 1) / 2
        val t = typeVarGenerator.getUnique
        val tupArgs = for {
          _ <- 1 to n
          v <- List(BoolT, t)
        } yield v

        List(PolyOperT(List(t), OperT(TupT(t +: tupArgs: _*), t)))

      /** Oper */
      case TlaOper.apply =>
        val n = operEx.args.length - 1
        val t = typeVarGenerator.getUnique
        if (n == 0) {
          List(PolyOperT(List(t), OperT(TupT(t), t)))
        } else {
          val ts = typeVarGenerator.getNUnique(n)
          List(
            PolyOperT(t +: ts, OperT(TupT(OperT(TupT(ts: _*), t) +: ts: _*), t))
          )
        }

      /** Sequences */
      // TODO
      /** Overloaded */
      case TlaFunOper.app =>
        // TODO: Application has multiple signatures
        val ts = typeVarGenerator.getNUnique(2)
        val List(t1, t2) = ts
        List(PolyOperT(ts, OperT(TupT(FunT(t1, t2), t1), t1)))

      case TlaFunOper.except =>
        // Todo, EXCEPT has multiple signatures

        val n = (operEx.args.length - 1) / 2
        val tupSizes = operEx.args.zipWithIndex.collect {
          case (OperEx(TlaFunOper.tuple, tupargs @ _*), i) if i % 2 == 1 =>
            tupargs.length
        }.toSet
        assert(tupSizes.size == 1)
        // All of the arguments are k-tuples
        val k = tupSizes.head
        val t = typeVarGenerator.getUnique
        val ts = typeVarGenerator.getNUnique(k)
        val fnChain = ts.foldRight[TlaType](t) {
          case (from, to) => FunT(from, to)
        }
        val allPairs = for {
          _ <- 1 to n
          v <- List(TupT(ts: _*), t)
        } yield v
        List(PolyOperT(t +: ts, OperT(TupT(fnChain +: allPairs: _*), fnChain)))

      case o =>
        throw new IllegalArgumentException(
          s"Signature of operator ${o.toString} is not known"
        )
    }
}
