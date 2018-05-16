class float1
{
  public static void main(String[] args)
  {
    java.util.Random random = new java.util.Random(42);
    
    float f=random.nextFloat();

    // conversions
    int i=(int)f;
    char c=(char)f;
    long l=(long)f;
    double d=f;
    short s=(short)f;
    
    // constants
    f=1.1234f;
    f=java.lang.Float.POSITIVE_INFINITY;
    f=java.lang.Float.NEGATIVE_INFINITY;
    f=java.lang.Float.NaN;
  }
}

