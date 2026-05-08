public class Test {

  public static void test(String[] args) {

    Object[][] ts = new Test[1][1];
    Object[][] subs = new Sub[1][1];
    assert subs instanceof Test[][];
    assert subs instanceof Sub[][];
    assert subs instanceof Object[][];
    assert subs instanceof Object[];
    assert subs instanceof Object;
    assert ts instanceof Test[][];
    assert ts instanceof Object[][];
    assert ts instanceof Object[];
    assert ts instanceof Object;
    assert ts instanceof Sub[][];
  }
}

class Sub extends Test {}
