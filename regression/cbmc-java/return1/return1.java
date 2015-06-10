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

  public static void main(String[] args)
  {
    short s = short_value();
    if(s == 1)
      if(bool_value())
        assert false;
  }
}

