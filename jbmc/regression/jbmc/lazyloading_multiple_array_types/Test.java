public class Test {
  
  A[] arrayA;
  B[] arrayB;

  public static void check(Test t) {
    if (t == null || t.arrayA == null || t.arrayB == null ||
        t.arrayA.length == 0 || t.arrayB.length == 0 ||
        t.arrayA[0] == null || t.arrayB[0] == null)
      return;
    int i = t.arrayA[0].f();
    int j = t.arrayB[0].g();
    int sum = i + j;
    assert(sum == 6);
  }

}
