public class Test {

  public static void test(boolean unknown) {

    Object[] tarrays = new Test[1][1];
    Object[] ts = new Test[1];
    assert ts instanceof Test[];
    assert tarrays instanceof Test[][];
    if (unknown)
      assert ts instanceof Test[][];
    else
      assert tarrays instanceof Test[];
  }
}
