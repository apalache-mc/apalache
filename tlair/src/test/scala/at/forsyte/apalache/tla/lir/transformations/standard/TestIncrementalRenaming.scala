package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.scalacheck.Prop.{falsified, forAll, passed}
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfter, FunSuite}

class TestIncrementalRenaming extends FunSuite with BeforeAndAfter with Checkers {
  type CounterMap = Map[String, Int]

  private val emptyCounters: CounterMap = Map.empty

  test("no duplicate definitions after incremental renaming") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 10
    }

    val prop = {
      val ops = gens.simpleOperators ++ gens.arithOperators ++ gens.setOperators
      val exGen = gens.genTlaEx(ops)(_)
      forAll(gens.genTlaModule(exGen)) { input =>
        try {
          val output = new IncrementalRenaming(new IdleTracker()).renameInModule(input)
          val multiset = output.operDeclarations.foldLeft(emptyCounters) { case (set, d) =>
            set ++ collectDefined(d.body)
          }
          multiset.find { case (_, i) => i > 1 } match {
            case None            => passed
            case Some((name, n)) => falsified :| s"Name $name is defined $n times"
          }
        } catch {
          // the generator has produced a malformed expression
          case _: MalformedTlaError => passed
        }
      }
    }

    check(prop, minSuccessful(10000), sizeRange(10))
  }

  // Collect a multiset of defined names. Every name is assigned the number of times it has been defined.
  private def collectDefined: TlaEx => CounterMap = {
    // one way to introduce new names is to write LET Foo(...) == ... IN ...
    case LetInEx(body, decls @ _*) =>
      decls.foldLeft(collectDefined(body)) { (map, d) =>
        incrementKey(map, d.name)
      }

    // Another way is to bind a name to a set element as in \E x \in S: P.
    // Here we assume that the expressions have been de-sugared, that is, there are no tuples of names.
    case OperEx(oper, NameEx(varName), set, pred)
        if oper == TlaOper.chooseBounded || oper == TlaBoolOper.forall || oper == TlaBoolOper.exists
          || oper == TlaSetOper.filter =>
      incrementKey(addMaps(collectDefined(set), collectDefined(pred)), varName)

    // Finally, a few operators bind multiple variables.
    // Again, we assume that the expressions have been de-sugared, that is, there are no tuples of names.
    case ex @ OperEx(oper, args @ _*) if oper == TlaSetOper.map || oper == TlaFunOper.funDef =>
      val (vars, sets) =
        try {
          TlaOper.deinterleave(args)
        } catch {
          // Desugarer produces the right arguments
          case _: AssertionError => throw new MalformedTlaError("it should be desugared", ex)
        }
      val names = vars.collect { case NameEx(name) => name }

      if (names.length != sets.length) {
        // the test data is malformed, ignore
        emptyCounters
      } else {
        val namesMap = names.map(_ -> 1).toMap
        sets.foldLeft(namesMap) { case (map, set) => map ++ collectDefined(set) }
      }

    // the other operators may contain definitions in their arguments
    case OperEx(_, args @ _*) =>
      args.foldLeft(emptyCounters) { case (map, arg) => map ++ collectDefined(arg) }

    // the rest are not interesting
    case _ =>
      emptyCounters
  }

  private def incrementKey(map: CounterMap, key: String): CounterMap = {
    map + (key -> (1 + map.getOrElse(key, 0)))
  }

  private def addMaps(left: CounterMap, right: CounterMap): CounterMap = {
    right.foldLeft(left) { case (map, (key, countInRight)) =>
      map + (key -> (countInRight + map.getOrElse(key, 0)))
    }
  }
}
