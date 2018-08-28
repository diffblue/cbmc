public class TestClass {
  public static void f(int y) {
    if(y < 1)
      return;
    float[][] a1 = new float[y][3];
    int j = 0;
    a1[j][0] = 34.5f;
    assert a1[0][j] > 0;
  }
}
