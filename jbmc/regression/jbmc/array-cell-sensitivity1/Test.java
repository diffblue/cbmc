public class Test {

  public static void main(int unknown) {

    int[] x = new int[10];
    x[unknown] = 1;
    x[1] = unknown;
    assert (x[1] == unknown);
  }
}
