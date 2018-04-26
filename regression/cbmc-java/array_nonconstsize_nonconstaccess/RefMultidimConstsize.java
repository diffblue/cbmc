public class RefMultidimConstsize {
  public void f(int y) {
    A[][] a1 = new A[2][2];
    int j = 1;
    a1[j][1] = new A();
    a1[j][1].a = 1.0f;
  }
}
