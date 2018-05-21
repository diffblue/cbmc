class __CPROVER
{
  public static float __java_bytecode_frem(float numerator, float denominator) {
    assert numerator > -2.6f && numerator < -2.4f && denominator > 0.4f && denominator < 0.6f;
    return -0.0f;
  }

  public static double __java_bytecode_drem(double numerator, double denominator) {
    assert numerator > -2.6 && numerator < -2.4 && denominator > 0.4 && denominator < 0.6;
    return -0.0;
  }
}

class farith1
{
  public static void main(String[] args)
  {
    float f = 2.5f;
    f = -f;
    ++f;
    f -= 1.0f;
    f *= 2.0f;
    f /= 2.0f;
    f %= 0.5f;
    assert f > -0.1f && f < 0.1f;
    double d = 2.5;
    d = -d;
    ++d;
    d -= 1.0;
    d *= 2.0;
    d /= 2.0;
    d %= 0.5;
    assert d > -0.1 && d < 0.1;
  }
}
