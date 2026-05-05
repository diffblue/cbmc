class double1
{
  public static void main(String[] args)
  {
    java.util.Random random = new java.util.Random(42);
    
    double d=random.nextDouble();

    // conversions
    int i=(int)d;
    char c=(char)d;
    long l=(long)d;
    float f=(float)d;
    short s=(short)d;
    
    // constants
    d=1.1234;
    d=java.lang.Double.POSITIVE_INFINITY;
    d=java.lang.Double.NEGATIVE_INFINITY;
    d=java.lang.Double.NaN;
  }

  public static String testLimit(double inputValue) {
    if(0x1p-1022 == inputValue){
      assert(false);
      return "reach";
    }
    return "default";
  }
}

