package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaDecl;
import at.forsyte.apalache.tla.lir.TlaModule;
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker;
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy;
import java.util.List;
import java.util.Objects;
import scala.jdk.javaapi.CollectionConverters;

/**
 * Creates, inspects and copies TLA+ modules made from existing declarations.
 *
 * <p>Module creation preserves declaration order and does not copy, resolve or type-check the
 * supplied declarations.</p>
 */
public final class TlaModules {
  private TlaModules() {}

  /** Snapshots declaration order, retaining the supplied declarations without deep copying. */
  public static TlaModule create(String name, List<? extends TlaDecl> declarations) {
    var snapshot = List.<TlaDecl>copyOf(declarations);
    return TlaModule.apply(
        Objects.requireNonNull(name), CollectionConverters.asScala(snapshot).toSeq());
  }

  /** Immutable snapshot; declaration elements remain mutable IR objects. */
  public static List<TlaDecl> declarations(TlaModule module) {
    return List.copyOf(CollectionConverters.asJava(module.declarations()));
  }

  /** Copies declarations and their expressions with fresh IDs and no mutable declaration sharing. */
  public static TlaModule deepCopy(TlaModule module) {
    return new DeepCopy(new IdleTracker()).deepCopyModule(module);
  }
}
