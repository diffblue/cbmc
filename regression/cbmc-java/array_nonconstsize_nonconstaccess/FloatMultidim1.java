public class FloatMultidim1 {
  public float[][] f(int y) {
    if (y > 0 && y < 5) {
      float[][] a1 = new float[y][2];
      int j;
      if (y > 1) {
        j = 1;
      } else {
        j = 0;
      }
      a1[j][1] = 1.0f;
      return a1;
    } else {
      return null;
    }
  }
}
