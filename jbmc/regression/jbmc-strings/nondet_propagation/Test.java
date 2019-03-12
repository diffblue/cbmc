public class Test {
  public String foo() {
    final int i = 10;
    final String retval = Integer.toHexString(i);
    assert(false);
    return retval;
  }
}
