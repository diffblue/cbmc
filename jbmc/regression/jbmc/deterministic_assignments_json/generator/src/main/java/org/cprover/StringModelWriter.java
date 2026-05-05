package org.cprover;

import com.cedarsoftware.util.io.JsonWriter;

import java.io.IOException;
import java.io.Writer;

import static com.cedarsoftware.util.io.JsonWriter.writeJsonUtf8String;

/**
 * This duplicates JsonStringWriter from json-io.
 * json-io has a check for JsonStringWriter which results in never printing its type.
 * We avoid this check by having our own custom writer for strings.
 */
public class StringModelWriter implements JsonWriter.JsonClassWriter {

  public void write(Object obj, boolean showType, Writer output) throws IOException {
    output.write("\"value\":");
    writeJsonUtf8String((String) obj, output);
  }

  public boolean hasPrimitiveForm() { return true; }

  public void writePrimitiveForm(Object o, Writer output) throws IOException {
    writeJsonUtf8String((String) o, output);
  }
}
