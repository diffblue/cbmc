public class RefMultidim2 {
  public A[][] f(int y) {
    if (y > 0 && y < 5) {
      A[][] a1 = new A[2][y];
      int j;
      if (y > 1) {
        j = 1;
      } else {
        j = 0;
      }
      a1[1][j] = new A();
      a1[1][j].a = 1.0f;
      return a1;
    } else {
      return null;
    }
  }
}
