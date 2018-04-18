class shift1
{
  public static void main(String[] args)
  {
    assert (5 << 1) == 10;
    assert (5 >> 1) == 2;
    assert (-4 >> 1) == -2;
    assert (-4 >>> 1) == 2147483646;
  }
}

