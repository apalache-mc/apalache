package at.forsyte.apalache.tla.typecheck.etcfast

import at.forsyte.apalache.tla.typecheck.TypeChecker
import at.forsyte.apalache.tla.typecheck.etc.TestEtcTypeCheckerBase
import at.forsyte.apalache.tla.types.TypeVarPool
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestEtcTypeCheckerFast extends TestEtcTypeCheckerBase {
  override protected def mkChecker(): TypeChecker = new EtcTypeCheckerFast(new TypeVarPool(start = 1000))
  override protected def strictListenerTypes: Boolean = false
  override protected def strictWarnings: Boolean = false
}
