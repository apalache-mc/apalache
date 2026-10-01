package org.apalache_mc.tla.jio;

import at.forsyte.apalache.io.annotations.PrettyWriterWithAnnotations;
import at.forsyte.apalache.io.lir.PrettyWriter;
import at.forsyte.apalache.io.lir.TextLayout;
import at.forsyte.apalache.io.lir.TlaDeclAnnotator;
import at.forsyte.apalache.io.lir.TlaWriter;
import at.forsyte.apalache.tla.lir.TlaEx;
import at.forsyte.apalache.tla.lir.TlaModule;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.Objects;
import java.util.function.Consumer;
import scala.jdk.javaapi.CollectionConverters;

/**
 * Formats typed TLA+ expressions and modules with a reusable text layout.
 *
 * <p>Use {@code write(TlaEx, PrintWriter)} or a module-writing overload when writing to
 * an existing destination. Use {@code render(Consumer)} to capture a write operation as
 * a string.</p>
 */
public final class TlaText {
  private final TextLayout layout;

  /**
   * Creates a formatter with the supplied layout.
   *
   * @param textWidth maximum preferred line width in characters
   * @param indent spaces in one indentation level
   * @throws IllegalArgumentException if the width is not positive or indentation is negative
   */
  public TlaText(int textWidth, int indent) {
    if (textWidth <= 0 || indent < 0) {
      throw new IllegalArgumentException("Text width must be positive and indentation nonnegative");
    }
    layout = new TextLayout(textWidth, indent);
  }

  /**
   * Writes an expression without declaration annotations.
   *
   * @param expression the expression to format
   * @param writer the destination, which remains open and is not flushed
   */
  public void write(TlaEx expression, PrintWriter writer) {
    Objects.requireNonNull(expression);
    Objects.requireNonNull(writer);
    new PrettyWriter(writer, layout, new TlaDeclAnnotator()).write(expression);
  }

  /**
   * Writes a module with type annotations and Apalache's standard extension modules.
   *
   * @param module the module to format
   * @param writer the destination, which remains open and is not flushed
   */
  public void writeWithStandard(TlaModule module, PrintWriter writer) {
    write(module, standardModules(), writer);
  }

  /**
   * Writes a typed module with explicit extension modules in the supplied order.
   *
   * @param module the module to format
   * @param extendedModules module names to emit in the {@code EXTENDS} clause
   * @param writer the destination, which remains open and is not flushed
   */
  public void write(TlaModule module, List<String> extendedModules, PrintWriter writer) {
    Objects.requireNonNull(module);
    Objects.requireNonNull(writer);
    var extensions = List.copyOf(extendedModules);
    new PrettyWriterWithAnnotations(
        at.forsyte.apalache.io.annotations.store.package$.MODULE$.createAnnotationStore(),
        writer, layout)
        .write(module, CollectionConverters.asScala(extensions).toList());
  }

  /**
   * Runs a write operation against an in-memory destination and returns its text.
   *
   * <p>For example: {@code text.render(writer -> text.write(expression, writer))}.</p>
   * The callback must complete synchronously and must not retain the supplied writer.
   *
   * @param writeOperation an operation that writes using this formatter
   * @return all text written by the operation
   */
  public String render(Consumer<PrintWriter> writeOperation) {
    Objects.requireNonNull(writeOperation);
    var output = new StringWriter();
    try (var writer = new PrintWriter(output)) {
      writeOperation.accept(writer);
      writer.flush();
      return output.toString();
    }
  }

  /**
   * Returns the extension module names used by
   * {@link #writeWithStandard(TlaModule, PrintWriter)}.
   *
   * @return an immutable list in output order
   */
  public static List<String> standardModules() {
    return List.copyOf(CollectionConverters.asJava(TlaWriter.STANDARD_MODULES()));
  }

}
