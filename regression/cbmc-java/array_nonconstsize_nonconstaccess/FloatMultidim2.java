public class FloatMultidim2 {
  public float[][] f(int y) {
    if (y > 0 && y < 5) {
      float[][] a1 = new float[2][y];
      int j;
      if (y > 1) {
        j = 1;
      } else {
        j = 0;
      }
      a1[1][j] = 1.0f;
      return a1;
    } else {
      return new float[1][1];
    }
  }
}
