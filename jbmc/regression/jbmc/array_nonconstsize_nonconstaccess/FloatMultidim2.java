public class FloatMultidim2 {
  public float[][] f(int y) {
    float[][] a1 = null;
    if (y > 0 && y < 5) {
      a1 = new float[2][y];
      int j;
      if (y > 1) {
        j = 1;
      } else {
        j = 0;
      }
      a1[1][j] = 1.0f;
    }
    assert a1 == null;
    return a1;
  }
}
