package org.apalache_mc.tla.jio;

import static org.junit.Assert.*;

import at.forsyte.apalache.tla.lir.*;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.math.BigInteger;
import java.util.List;
import org.apalache_mc.tla.jir.*;
import org.junit.Test;

public final class IoFacadeTest {
  @Test
  public void typedModulesRoundTripThroughJson() {
    var b = new TlaTypedScopeUncheckedBuilder();
    var a = TlaTypes.typeVariable(0);
    var empty = b.emptySet(a);
    var local = b.decl("Empty", empty);
    var body = TlaExpressions.letIn(
        b.label(b.integer(new BigInteger("123456789012345678901234567890")), "Label"), List.of(local));
    var record = TlaDeclarations.variable("r", TlaTypes.rowRecord(a, new NamedType("n", TlaTypes.INT)));
    var variant = TlaDeclarations.variable("v", TlaTypes.variant(a, new NamedType("Some", TlaTypes.INT)));
    var module = TlaModules.create("JavaIo", List.of(record, variant, b.decl("Value", body)));

    var decoded = TlaJson.readModule(TlaJson.writeModule(module, 2));
    assertEquals("JavaIo", decoded.name());
    var definitions = TlaModules.declarations(decoded);
    assertEquals(TlaTypes.typeOf(record), TlaTypes.typeOf(definitions.get(0)));
    assertEquals(TlaTypes.typeOf(variant), TlaTypes.typeOf(definitions.get(1)));
    var decodedBody = (LetInEx) ((TlaOperDecl) definitions.get(2)).body();
    assertSame(TlaOperators.LABEL, ((OperEx) decodedBody.body()).oper());
    var decodedEmpty = TlaExpressions.localDeclarations(decodedBody).getFirst().body();
    assertEquals(TlaTypes.set(a), TlaTypes.typeOf(decodedEmpty));
    assertTrue(TlaJson.writeModule(decoded, -1).contains("123456789012345678901234567890"));
  }

  @Test
  public void expressionsAndModulesRenderAsTlaText() {
    var b = new TlaTypedScopeUncheckedBuilder();
    var module = TlaModules.create("JavaIo", List.of(b.decl("Value", b.integer(1))));
    var text = new TlaText(80, 2);
    var source = text.render(writer -> text.writeWithStandard(module, writer));
    assertTrue(source.contains("MODULE JavaIo"));
    assertTrue(source.contains("@type:"));
    var expression = b.plus(b.integer(1), b.integer(2));
    assertTrue(text.render(writer -> text.write(expression, writer)).contains("1 + 2"));

    var wideText = new TlaText(120, 4);
    assertTrue(wideText.render(writer -> wideText.write(module, List.of("Integers"), writer))
        .contains("EXTENDS Integers"));
    var output = new StringWriter();
    var writer = new PrintWriter(output);
    wideText.write(module, List.of("Integers"), writer);
    writer.flush();
    assertTrue(output.toString().contains("EXTENDS Integers"));
    writer.print("still open");
    writer.flush();
    assertTrue(output.toString().endsWith("still open"));
  }

  @Test
  public void malformedJsonAndIrRetainTheirCauses() {
    for (var invalid : List.of("{", "{}", "[]")) {
      var exception = assertThrows(TlaJsonException.class, () -> TlaJson.readModule(invalid));
      assertNotNull(exception.getCause());
    }
  }
}
