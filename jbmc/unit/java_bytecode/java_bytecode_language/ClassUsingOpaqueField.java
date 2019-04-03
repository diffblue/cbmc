public class ClassUsingOpaqueField {
  public static int opaqueFieldMethod() {
    OpaqueClass o = new OpaqueClass();
    return OpaqueClass.field1 + o.field2;
  }
}
