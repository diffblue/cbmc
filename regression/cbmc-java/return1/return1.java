class return1
{
  public static short short_value()
  {
    short s = 1;
    return s;
  }

  public static boolean bool_value()
  {
    boolean b = true;
    return b;
  }

  public static long long_value()
  {
    long l = 0x10000ffffl;
    return l;
  }

  public static void main(String[] args)
  {
    short s = short_value();
    if(s == 1)
      if(bool_value())
        if(long_value()==0x10000ffffl)
          assert false;
  }
}

