package org.cprover;

import com.cedarsoftware.util.io.JsonWriter;

import java.io.IOException;
import java.io.Writer;
import java.util.Iterator;
import java.util.Map;

import static com.cedarsoftware.util.io.JsonWriter.JsonClassWriterEx.Support.getWriter;

public class StaticFieldMapWriter implements JsonWriter.JsonClassWriterEx {

  public void write(Object obj, boolean showType, Writer output, Map<String, Object> args)
    throws IOException {
    StaticFieldMap<?> map = (StaticFieldMap<?>) obj;
    writeHelper(map, output, args);
  }

  private <V> void writeHelper(StaticFieldMap<V> map, Writer output, Map<String, Object> args)
    throws IOException {
    JsonWriter outerWriter = getWriter(args);
    // Make sure the output is still valid JSON if we (accidentally) try to write an empty map.
    if (map.isEmpty()) {
      output.write("\"@noFields\": true");
      return;
    }
    Iterator<Map.Entry<String, V>> it = map.entrySet().iterator();
    Map.Entry<String, V> entry = it.next();
    output.write('"' + entry.getKey() + "\":");
    outerWriter.writeImpl(entry.getValue(), true, true, true);
    while (it.hasNext()) {
      output.write(',');
      entry = it.next();
      output.write('"' + entry.getKey() + "\":");
      outerWriter.writeImpl(entry.getValue(), true, true, true);
    }
  }
}
