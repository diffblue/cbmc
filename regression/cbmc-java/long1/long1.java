class long1
{
  public static void main(String[] args)
  {
    java.util.Random random = new java.util.Random(42);
    
    long l=random.nextLong();

    // conversions
    int i=(int)l;
    char c=(char)l;
    float f=l;
    double d=l;
    short s=(short)l;
    
    if(l>=0)
    {
      assert (long)i==(l&0x7fffffff);
      assert (long)c==(l&0xffff);
      assert (long)s==(l&0x7fff);
    }
  }
}

