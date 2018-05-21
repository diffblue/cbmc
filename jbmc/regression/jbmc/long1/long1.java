class long1
{
  public static void main(String[] args)
  {
    java.util.Random random = new java.util.Random(42);
    
    //long l=random.nextLong();
    long l=4620693217682128896L;

    // conversions
    int i=(int)l;
    char c=(char)l;
    float f=l;
    double d=l;
    short s=(short)l;

    if(i>=0)
      assert (long)i==(l&0x7fffffff);

    if(c>=0)
      assert (long)c==(l&0x7fff);

    if(s>=0)
      assert (long)s==(l&0x7fff);
  }
}

