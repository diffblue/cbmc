public class test {

  public int field;

  public test(int value) {

    field = value;

  }

  public static void main(boolean unknown) {

    test t = new test(12345);
    test maybe_t = unknown ? null : t;

    // t could still be null, but symex ought to notice that as the Java frontend introduces
    // checks before all pointer dereference operations, it can statically eliminate
    // the assertion below.

    int field_value = maybe_t.field;
    assert field_value == 12345;

  }

}
