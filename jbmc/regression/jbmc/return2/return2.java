class return2
{
  public static void main(String[] args)
  {
    try
    {
      int v1=System.in.read();
      int v2=System.in.read();
      assert v1==v2; // should be able to fail
    }
    catch(java.io.IOException e)
    {
    }
  }
}

