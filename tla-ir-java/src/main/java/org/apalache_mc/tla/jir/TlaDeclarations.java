package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaConstDecl;
import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.lir.TlaVarDecl;
import org.apalache_mc.tla.jir.impl.JavaToScalaAdapter$;

/** Creates typed TLA+ constant and variable declarations for use in Apalache IR. */
public final class TlaDeclarations {
  /** Prevents instantiation. */
  private TlaDeclarations() {}

  /**
   * Returns a declaration for a TLA+ constant with the supplied type.
   *
   * @param name the constant name as it appears in TLA+
   * @param type the constant's type
   * @return the typed constant declaration
   */
  public static TlaConstDecl constant(String name, TlaType1 type) {
    return JavaToScalaAdapter$.MODULE$.constantDeclaration(name, type);
  }

  /**
   * Returns a declaration for a TLA+ variable with the supplied type.
   *
   * @param name the variable name as it appears in TLA+
   * @param type the variable's type
   * @return the typed variable declaration
   */
  public static TlaVarDecl variable(String name, TlaType1 type) {
    return JavaToScalaAdapter$.MODULE$.variableDeclaration(name, type);
  }
}
