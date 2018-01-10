public class InstanceOf8 {
  public static boolean test(Integer i) {
    if (i instanceof Integer) {
      return true;
    } else {
      return false;
    }
  }
  public static void main(String[] args)
  {
    assert(!test(null));
    assert(test(new Integer(1)));
  }
}
