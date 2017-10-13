
public class CustomVSATest {

  public Object never_read;

  public static Object cause;
  public static Object effect;
  public static Object first_effect_read;
  public static Object second_effect_read;
  public static Object maybe_unknown_read;

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
    maybe_unknown_read=maybe_unknown;

    effect = new Object();
    first_effect_read = effect;

    // Under our custom VSA, this write should cause effect to become null:
    cause = new Object();
    second_effect_read = effect;

  }

}
