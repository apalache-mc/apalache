package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.TypeChecker
import at.forsyte.apalache.tla.types.TypeVarPool
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestEtcTypeChecker extends TestEtcTypeCheckerBase {
  override protected def mkChecker(): TypeChecker = new EtcTypeChecker(new TypeVarPool(start = 1000))
}
