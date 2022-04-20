//package at.forsyte.apalache.tla.typecmp
//
//import at.forsyte.apalache.tla.lir._
//import at.forsyte.apalache.tla.lir.oper.TlaFunOper
//import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaStr}
//import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
//import org.junit.runner.RunWith
//import org.scalatest.BeforeAndAfter
//import org.scalatest.funsuite.AnyFunSuite
//import org.scalatestplus.junit.JUnitRunner
//
//@RunWith(classOf[JUnitRunner])
//class TestTypeCalculatingBuilder extends AnyFunSuite with BeforeAndAfter {
//
//  var varPool = new TypeVarPool()
//  var sigGen = new SignatureGenerator(varPool)
//  var builder = new TypeCalculatingBuilder(sigGen)
//  var builderM = new ScopedBuilder(sigGen)
//
//  before {
//    varPool = new TypeVarPool()
//    sigGen = new SignatureGenerator(varPool)
//    builder = new TypeCalculatingBuilder(sigGen)
//  }
//
//  test("Except") {
//    val except = FunOp.exceptCmp
//
//    val recType = RecT1("y" -> IntT1())
//    val recExceptArgs = Seq(
//        NameEx("x")(Typed(recType)),
//        OperEx(
//            TlaFunOper.tuple,
//            ValEx(TlaStr("y"))(Typed(StrT1())),
//        )(Typed(TupT1(StrT1()))),
//        NameEx("z")(Typed(IntT1())),
//    )
//
//    val resRec = except(recExceptArgs)
//    assert(resRec.contains(recType))
//  }
//
//}
