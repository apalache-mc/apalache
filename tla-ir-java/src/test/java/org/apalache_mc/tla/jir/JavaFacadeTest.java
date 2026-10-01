package org.apalache_mc.tla.jir;

import static org.junit.Assert.*;

import at.forsyte.apalache.tla.lir.*;
import java.util.*;
import java.util.function.UnaryOperator;
import org.junit.Test;

public final class JavaFacadeTest {
  @Test
  public void typesCanBeConstructedAndInspected() {
    var checked = new TlaCheckedBuilder();
    assertEquals(TlaTypes.INT, TlaTypes.typeOf(checked.build(checked.plus(checked.integer(1), checked.integer(2)))));
    assertThrows(TlaBuilderTypeException.class,
        () -> checked.build(checked.plus(checked.bool(true), checked.integer(1))));

    var a = TlaTypes.typeVariable(91);
    var row = TlaTypes.row(a, new NamedType("z", TlaTypes.INT), new NamedType("a", TlaTypes.BOOL));
    assertEquals(List.of("a", "z"), new ArrayList<>(TlaTypes.rowFields(row).keySet()));
    assertEquals(List.of(TlaTypes.BOOL, TlaTypes.INT, a), TlaTypes.children(row));
    assertEquals(Optional.of(a), TlaTypes.rowTail(row));
    assertEquals(Set.of(91), TlaTypes.usedVariables(row));
    assertThrows(UnsupportedOperationException.class, () -> TlaTypes.rowFields(row).put("x", a));
    assertEquals(List.of(), TlaTypes.children(TlaTypes.REAL));
    assertEquals(List.of(TlaTypes.BOOL, TlaTypes.INT), TlaTypes.children(TlaTypes.sparseTuple(
        new IndexedType(4, TlaTypes.INT), new IndexedType(2, TlaTypes.BOOL))));
    assertEquals(List.of(TlaTypes.INT, TlaTypes.BOOL),
        TlaTypes.tupleElements(TlaTypes.tuple(TlaTypes.INT, TlaTypes.BOOL)));
    var operatorType = TlaTypes.operator(TlaTypes.BOOL, TlaTypes.INT);
    assertEquals(List.of(TlaTypes.INT), TlaTypes.operatorArguments(operatorType));
    assertEquals(List.of(TlaTypes.INT, TlaTypes.BOOL), TlaTypes.children(operatorType));
    assertEquals(Optional.empty(), TlaTypes.rowTail(TlaTypes.row()));
  }

  @Test
  public void expressionsDeclarationsAndModulesCanBeTransformed() {
    var b = new TlaTypedScopeUncheckedBuilder();
    var one = b.integer(1);
    var name = (NameEx) b.name("x", TlaTypes.INT);
    var decl = b.decl("Identity", name, b.param("x", TlaTypes.INT));
    var let = TlaExpressions.letIn(one, List.of(decl));
    var visited = new ArrayList<TlaEx>();
    TlaExpressions.forEach(let, visited::add);
    assertEquals(List.of(let, one, name), visited);

    var rewritten = (LetInEx) TlaExpressions.rewrite(let, UnaryOperator.identity());
    assertNotSame(let, rewritten);
    assertSame(one, rewritten.body());
    assertNotSame(decl, TlaExpressions.localDeclarations(rewritten).getFirst());
    var copied = (LetInEx) TlaExpressions.deepCopy(let);
    assertNotSame(one, copied.body());
    assertNotEquals(one.ID(), copied.body().ID());

    var renamed = TlaDeclarations.withHeader(decl, "Other", List.of("y"));
    assertEquals(List.of(new TypedParameter("y", TlaTypes.INT)), TlaDeclarations.parameters(renamed));
    assertEquals(TlaTypes.typeOf(decl), TlaTypes.typeOf(renamed));
    assertThrows(IllegalArgumentException.class, () -> TlaDeclarations.withHeader(decl, "Other", List.of()));
    var newBody = TlaExpressions.withName(name, "y");
    assertEquals(newBody, TlaDeclarations.withBody(renamed, newBody).body());
    var changed = TlaDeclarations.rewrite(decl,
        ex -> ex instanceof NameEx n ? TlaExpressions.withName(n, "y") : ex);
    assertEquals("y", ((NameEx) changed.body()).name());

    var args = new ArrayList<TlaEx>(List.of(one, b.integer(2)));
    var plus = (OperEx) b.plus(one, one);
    var newPlus = TlaExpressions.withArguments(plus, args);
    args.clear();
    assertEquals(2, TlaExpressions.arguments(newPlus).size());
    assertSame(TlaOperators.PLUS, newPlus.oper());
    assertThrows(UnsupportedOperationException.class, () -> TlaExpressions.arguments(newPlus).clear());

    var moduleDecls = new ArrayList<TlaDecl>(List.of(decl));
    var module = TlaModules.create("M", moduleDecls);
    moduleDecls.clear();
    assertSame(decl, TlaModules.declarations(module).getFirst());
    assertNotSame(decl, TlaModules.declarations(TlaModules.deepCopy(module)).getFirst());
    assertEquals(TlaTypes.INT, TlaTypes.typeOf(one));
  }

  @Test
  public void substitutionsAndUnificationHaveIndependentState() {
    var v0 = TlaTypes.typeVariable(0);
    var v1 = TlaTypes.typeVariable(1);
    var simultaneous = TlaTypeSubstitution.of(Map.of(0, v1, 1, TlaTypes.INT));
    assertEquals(v1, simultaneous.applyOnce(v0));
    assertEquals(TlaTypes.INT, simultaneous.applyFully(v0));
    var swapping = TlaTypeSubstitution.of(Map.of(0, v1, 1, v0));
    assertEquals(TlaTypes.tuple(v1, v0), swapping.applyOnce(TlaTypes.tuple(v0, v1)));

    var unifier = new TlaTypeUnifier();
    var solved = unifier.unify(Optional.empty(), v0, TlaTypes.INT).orElseThrow();
    assertEquals(TlaTypes.INT, solved.unifiedType());
    assertEquals(TlaTypes.INT, solved.substitution().applyFully(v0));
    assertTrue(unifier.unify(Optional.empty(), TlaTypes.INT, TlaTypes.BOOL).isEmpty());
    assertTrue(unifier.unify(Optional.empty(), v0, TlaTypes.set(v0)).isEmpty());
    unifier.unify(Optional.empty(), v0, TlaTypes.BOOL).orElseThrow();
    assertEquals(TlaTypes.INT, solved.substitution().applyFully(v0));
    var exhausted = new TlaTypeUnifier(TlaTypes.typeVariable(Integer.MAX_VALUE));
    assertThrows(IllegalArgumentException.class, () -> exhausted.unify(Optional.empty(), v0, v1));

    var a = TlaTypes.typeVariable(91);
    var left = TlaTypes.rowRecord(v0, new NamedType("left", TlaTypes.INT));
    var right = TlaTypes.rowRecord(v1, new NamedType("right", TlaTypes.BOOL));
    var rows = new TlaTypeUnifier(a).unify(Optional.empty(), left, right).orElseThrow();
    var freshIds = new HashSet<>(TlaTypes.usedVariables(rows.unifiedType()));
    freshIds.removeAll(Set.of(0, 1));
    assertTrue(freshIds.stream().allMatch(id -> id > 91));
    assertFalse(freshIds.isEmpty());
    var fields = TlaTypes.rowFields(((RecRowT1) rows.unifiedType()).row());
    assertEquals(Set.of("left", "right"), fields.keySet());

    java.util.stream.IntStream.range(0, 32).parallel().forEach(i -> assertEquals(TlaTypes.INT,
        unifier.unify(Optional.of(simultaneous), v0, TlaTypes.INT).orElseThrow().unifiedType()));
  }
}
