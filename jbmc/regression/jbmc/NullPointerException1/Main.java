class Main
{
  public static void main(String[] args)
  {
    Object o=null;
    try
    {
      o.hashCode();
      // should pass
      assert false;
    }
    catch(Exception e)
    {
    }
  }
};
