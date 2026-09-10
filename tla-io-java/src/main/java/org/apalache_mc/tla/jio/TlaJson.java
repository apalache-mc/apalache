package org.apalache_mc.tla.jio;

import at.forsyte.apalache.io.json.DefaultTagJsonReader;
import at.forsyte.apalache.io.json.ujsonimpl.TlaToUJson$;
import at.forsyte.apalache.io.json.ujsonimpl.UJsonRepresentation;
import at.forsyte.apalache.io.json.ujsonimpl.UJsonToTla;
import at.forsyte.apalache.tla.lir.TlaModule;
import java.util.Objects;
import scala.Option;
import ujson.Readable;
import ujson.Value$;

/**
 * Converts between typed TLA+ modules and Apalache's JSON representation.
 *
 * <p>Round trips preserve encoded types and operator labels. This class works with JSON
 * strings; callers choose how files, streams and input-size limits are handled.</p>
 */
public final class TlaJson {
  private TlaJson() {}

  /**
   * Serializes one typed module as JSON.
   *
   * @param module the module to serialize
   * @param indent {@code -1} for compact JSON, or a nonnegative number of spaces for indentation
   * @return the JSON representation
   * @throws IllegalArgumentException if {@code indent} is less than {@code -1}
   */
  public static String writeModule(TlaModule module, int indent) {
    if (indent < -1) throw new IllegalArgumentException("Indentation must be -1 or nonnegative");
    var json = TlaToUJson$.MODULE$.apply(Objects.requireNonNull(module));
    return json.render(indent, false);
  }

  /**
   * Parses exactly one typed module from Apalache JSON.
   *
   * <p>Encoded type information is preserved as written; no type inference is performed.</p>
   *
   * @param json the JSON representation of one module
   * @return the decoded module
   * @throws TlaJsonException if the input is malformed or does not encode exactly one valid module
   */
  public static TlaModule readModule(String json) {
    Objects.requireNonNull(json);
    try {
      var readable = Readable.fromString(json);
      var value = readable.transform(Value$.MODULE$);
      var reader = new UJsonToTla(Option.empty(), DefaultTagJsonReader::apply);
      return reader.fromSingleModule(new UJsonRepresentation(value)).get();
    } catch (Exception cause) {
      throw new TlaJsonException("Invalid Apalache IR JSON: " + cause.getMessage(), cause);
    }
  }
}
