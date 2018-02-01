public class test {

  public static void main(int nondet) {

    float nan = 0.0f / 0.0f;
    float one = 1.0f;
    double nand = 0.0 / 0.0;
    double oned = 1.0;

    if(nondet == 1)
      checkeq(one, nan);
    if(nondet == 2)
      checkneq(one, nan);
    if(nondet == 3)
      checkgt(one, nan);
    if(nondet == 4)
      checkgeq(one, nan);
    if(nondet == 5)
      checklt(one, nan);
    if(nondet == 6)
      checkleq(one, nan);
    if(nondet == 7)
      checkeq(oned, nand);
    if(nondet == 8)
      checkneq(oned, nand);
    if(nondet == 9)
      checkgt(oned, nand);
    if(nondet == 10)
      checkgeq(oned, nand);
    if(nondet == 11)
      checklt(oned, nand);
    else
      checkleq(oned, nand);
  }

  public static void checkeq(float arg1, float arg2) {
    assert arg1 == arg2;
  }

  public static void checkneq(float arg1, float arg2) {
    assert arg1 != arg2;
  }

  public static void checkgt(float arg1, float arg2) {
    assert arg1 > arg2;
  }

  public static void checkgeq(float arg1, float arg2) {
    assert arg1 >= arg2;
  }

  public static void checklt(float arg1, float arg2) {
    assert arg1 < arg2;
  }

  public static void checkleq(float arg1, float arg2) {
    assert arg1 <= arg2;
  }

  public static void checkeq(double arg1, double arg2) {
    assert arg1 == arg2;
  }

  public static void checkneq(double arg1, double arg2) {
    assert arg1 != arg2;
  }

  public static void checkgt(double arg1, double arg2) {
    assert arg1 > arg2;
  }

  public static void checkgeq(double arg1, double arg2) {
    assert arg1 >= arg2;
  }

  public static void checklt(double arg1, double arg2) {
    assert arg1 < arg2;
  }

  public static void checkleq(double arg1, double arg2) {
    assert arg1 <= arg2;
  }

}
