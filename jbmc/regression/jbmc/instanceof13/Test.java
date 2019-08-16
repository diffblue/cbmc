public class Test {

  public static void test(String[] args) {

    Object[][] ts = new Test[1][1];
    Object[][] subs = new Sub[1][1];
    assert subs instanceof Test[][];
    assert subs instanceof Sub[][];
    assert ts instanceof Test[][];
    assert ts instanceof Sub[][];
  }
}

class Sub extends Test {}
