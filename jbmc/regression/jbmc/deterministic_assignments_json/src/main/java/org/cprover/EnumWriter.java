package org.cprover;

import com.cedarsoftware.util.io.JsonWriter;

import java.io.IOException;
import java.io.Writer;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Map;

import static com.cedarsoftware.util.io.JsonWriter.JsonClassWriterEx.Support.getWriter;

public class EnumWriter implements JsonWriter.JsonClassWriterEx {

  /**
   * Writes enums just like regular class types: by writing a key-value pair for all of its fields.
   * The difference to the standard way of writing enums in json-io is that the latter ignores the
   * ordinal field.
   */
  public void write(Object obj, boolean showType, Writer output, Map<String, Object> args)
    throws IOException {
    JsonWriter outerWriter = getWriter(args);
    Enum<?> enumm = (Enum<?>) obj;
    output.write("\"name\":\"" + enumm.name() + "\"");
    output.write(',');
    output.write("\"ordinal\":" + enumm.ordinal());
    for (Field field : enumm.getDeclaringClass().getDeclaredFields()) {
      if ((field.getModifiers() & Modifier.STATIC) != Modifier.STATIC) {
        output.write(",\"" + field.getName() + "\":");
        try {
          field.setAccessible(true);
          outerWriter.writeImpl(field.get(enumm), true, true, true);
        }
        catch (IllegalAccessException ex) {
          System.err.println("Could not access field " + field.getName() + " in class " +
            enumm.getDeclaringClass() + ".");
        }
      }
    }
  }
}
