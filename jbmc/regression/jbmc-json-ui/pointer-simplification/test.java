public class test {

  public static void main(String[] args) {

    test t = new test();
    test[] ts = new test[1];
    ts[0] = t;
    assert ts[0] == null;

  }

}
