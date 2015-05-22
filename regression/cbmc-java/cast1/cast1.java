class cast1
{
  public static void main(String[] args)
  {
    int i = 10;
    byte b = (byte) i;
    assert b == i;
    short s = (short) i;
    assert s == i;
    char c = (char) i;
    assert c == i;
    long l = (long) i;
    assert l == i;
    float f = (float) i;
    assert f == i;
    double d = (double) i;
    assert d == i;
    f = (float) d;
    assert (float) d == f;
    i = (int) d;
    assert (int) d == i;
    l = (long) d;
    assert i == l;
  }
}

