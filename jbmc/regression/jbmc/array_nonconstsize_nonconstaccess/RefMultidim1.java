public class RefMultidim1 {
  public A[][] f(int y) {
    A[][] a1 = null;
    if (y > 0 && y < 5) {
      a1 = new A[y][2];
      int j;
      if (y > 1) {
        j = 1;
      } else {
        j = 0;
      }
      a1[j][1] = new A();
      a1[j][1].a = 1.0f;
    }
    assert a1 == null;
    return a1;
  }
}
