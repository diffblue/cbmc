package org.cprover;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.*;

import com.cedarsoftware.util.io.JsonWriter;

public class JsonGenerator {

  /**
   * For all *.class files in the current directory, assuming one Java file per class file, write
   * the initial values of their static fields to the file clinit-state.json.
   */
  public static void main(String[] args) throws ClassNotFoundException, IOException {
    File here = new File(System.getProperty("user.dir"));
    File jsonFile = new File("clinit-state.json");
    StaticFieldMap<StaticFieldMap<Object>> classMap = new StaticFieldMap<>();
    for (File file : here.listFiles()) {
      if (file.getName().endsWith(".class")) {
        String className = classNameFromFile(file);
        StaticFieldMap<Object> staticFieldMap = staticFieldMap(Class.forName(className));
        if (!staticFieldMap.isEmpty()) {
          classMap.put(className, staticFieldMap);
        }
      }
    }
    Map<String, Object> jsonArgs = jsonWriterArgs();
    String json = JsonWriter.objectToJson(classMap, jsonArgs);
    FileWriter writer = new FileWriter(jsonFile);
    writer.write(json);
    writer.close();
  }

  public static Map<String, Object> jsonWriterArgs() {
    Map<String, Object> args = new HashMap<>();
    args.put(JsonWriter.WRITE_LONGS_AS_STRINGS, true);
    args.put(JsonWriter.PRETTY_PRINT, true);

    // We do not use json-io's shorthands for these types.
    Map<String, String> typeNameMap = new HashMap<>();
    typeNameMap.put("java.lang.Boolean", "java.lang.Boolean");
    typeNameMap.put("java.lang.Byte", "java.lang.Byte");
    typeNameMap.put("java.lang.Character", "java.lang.Character");
    typeNameMap.put("java.lang.Class", "java.lang.Class");
    typeNameMap.put("java.lang.Double", "java.lang.Double");
    typeNameMap.put("java.lang.Float", "java.lang.Float");
    typeNameMap.put("java.lang.Integer", "java.lang.Integer");
    typeNameMap.put("java.lang.Long", "java.lang.Long");
    typeNameMap.put("java.lang.Short", "java.lang.Short");
    typeNameMap.put("java.lang.String", "java.lang.String");
    typeNameMap.put("java.util.Date", "java.util.Date");
    args.put(JsonWriter.TYPE_NAME_MAP, typeNameMap);

    Map<Class, JsonWriter.JsonClassWriterBase> customWriters = new HashMap<>();
    customWriters.put(Enum.class, new EnumWriter());
    customWriters.put(String.class, new StringModelWriter());
    customWriters.put(StaticFieldMap.class, new StaticFieldMapWriter());
    args.put(JsonWriter.CUSTOM_WRITER_MAP, customWriters);
    return args;
  }

  /**
   * Assumes that a file MyClass.class contains exactly one Java class called MyClass.
   */
  public static String classNameFromFile(File file) {
    String fileName = file.getName();
    return fileName.substring(0, fileName.length() - 6);
  }

  public static StaticFieldMap<Object> staticFieldMap(Class<?> clazz) {
    StaticFieldMap<Object> staticFields = new StaticFieldMap<>();
    for (Field field : getDeclaredStaticFields(clazz)) {
      field.setAccessible(true);
      try {
        if (!field.getName().equals("$assertionsDisabled")) {
          staticFields.put(field.getName(), field.get(null));
        }
      }
      catch (IllegalAccessException e) {
        System.err.println("Could not access field " + field.getName() + " in class " +
            clazz.getName() + ".");
      }
    }
    return staticFields;
  }

  public static List<Field> getDeclaredStaticFields(Class<?> clazz) {
    List<Field> fields = new ArrayList<>();
    for (Field field : clazz.getDeclaredFields()) {
      if ((field.getModifiers() & Modifier.STATIC) == Modifier.STATIC) {
        fields.add(field);
      }
    }
    return fields;
  }
}
