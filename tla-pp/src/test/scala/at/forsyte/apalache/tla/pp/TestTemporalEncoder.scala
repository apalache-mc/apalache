// package at.forsyte.apalache.tla.pp

// import at.forsyte.apalache.tla.lir.TypedPredefs._
// import at.forsyte.apalache.tla.lir.convenience._
// import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
// import at.forsyte.apalache.tla.lir.{
//   BoolT1, FunT1, IntT1, OperParam, OperT1, RecT1, SeqT1, SetT1, StrT1, TlaEx, TlaType1, TupT1,
// }
// import org.junit.runner.RunWith
// import org.scalatestplus.junit.JUnitRunner
// import org.scalatest.BeforeAndAfterEach
// import org.scalatest.funsuite.AnyFunSuite

// import scala.collection.immutable.SortedMap

// @RunWith(classOf[JUnitRunner])
// class TestTemporalEncoder extends AnyFunSuite with BeforeAndAfterEach {
//   private var gen: UniqueNameGenerator = _
//   private var temporalEncoder: TemporalEncoder = _

//   private val varNames = Set(
//       "x",
//       "y",
//       "z",
//   )

//   override def beforeEach(): Unit = {
//     gen = new UniqueNameGenerator()
//     temporalEncoder = new TemporalEncoder(gen, varNames, new IdleTracker())
//   }

//   test("""X \intersect Y""") {
//     val types = Map("e" -> IntT1, "s" -> SetT1(IntT1), "b" -> BoolT1)
//     val input = tla
//       .cap(tla.name("X") ? "s", tla.name("Y") ? "s")
//       .typed(types, "s")
//     val output = temporalEncoder.apply(input)
//     val expected =
//       tla
//         .filter(tla.name("t_1") ? "e", tla.name("X") ? "s", tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b")
//         .typed(types, "s")
//     assert(expected == output)
//   }
// }
