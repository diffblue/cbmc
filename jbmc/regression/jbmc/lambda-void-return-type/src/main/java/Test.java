public class Test {

  public int lastArgument = 0;
  public int intToInt(int x) { lastArgument = x; return x + 1; }
  public Integer intToInteger(int x) { lastArgument = x; return x + 1; }
  public Object intToObject(int x) { lastArgument = x; return -1; }

  public interface IntToVoid {
    void consume(int x);
  }

  public static void test() {
    Test t = new Test();

    IntToVoid intToVoid = t::intToInt;
    intToVoid.consume(5);
    assert t.lastArgument == 5;

    IntToVoid intToVoid2 = t::intToInteger;
    intToVoid2.consume(10);
    assert t.lastArgument == 10;

    IntToVoid intToVoid3 = t::intToObject;
    intToVoid3.consume(15);
    assert t.lastArgument == 15;

    assert false; // Check we got here

  }

}
