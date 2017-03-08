
public class CustomVSATest {

  public Object never_read;
  public Object normal_field;
  public CustomVSATest unknown_field_ref;

  public static CustomVSATest unknown_global_ref;

  public static void test() {

    Object weak_local = new Object();
    // Under standard VSA the following should be a strong write;
    // with our test custom VSA it will be weak.
    weak_local = new Object();

    // Normally this would set the value of `ignored`, but our custom
    // VSA discards the instruction completely:
    Object ignored = new Object();

    // Similarly this write should have no effect:
    Object no_write = new Object();

    CustomVSATest vsa = new CustomVSATest();
    vsa.never_read = new Object();

    // Again this should be disregarded:
    Object read = vsa.never_read;

    // This should acquire a "*" unknown-object, even though
    // it is obvious what it points to:
    Object maybe_unknown = new Object();

    // Both of these fields, despite being initialised, should be
    // considered to point to some unknown target, and so the reads
    // through them return some unknown entity:

    CustomVSATest outer = new CustomVSATest();
    outer.unknown_field_ref = new CustomVSATest();
    outer.unknown_field_ref.normal_field = new Object();

    Object get_unknown_field = outer.unknown_field_ref.normal_field;

    unknown_global_ref = new CustomVSATest();
    unknown_global_ref.normal_field = new Object();

    Object get_unknown_global = unknown_global_ref.normal_field;

  }

}
