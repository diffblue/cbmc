package org.cprover;

public final class CProver
{
  public static boolean enableAssume=true;
  public static boolean enableNondet=true;

  public static boolean nondetBoolean()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetBoolean()");
    }

    return false;
  }

  public static byte nondetByte()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetByte()");
    }

    return 0;
  }

  public static char nondetChar()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetChar()");
    }
    
    return '\0';
  }

  public static short nondetShort()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetShort()");
    }

    return 0;
  }

  public static int nondetInt()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetInt()");
    }

    return 0;
  }

  public static long nondetLong()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetLong()");
    }

    return 0;
  }

  public static float nondetFloat()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetFloat()");
    }

    return 0;
  }

  public static double nondetDouble()
  {
    if (enableNondet)
    {
      throw new RuntimeException(
          "Cannot execute program with CProver.nondetDouble()");
    }

    return 0;
  }

  //  Set a variable to a nondeterminate state, which may be null.
  public static <T> void nondetWithNull(T t)
  {
    if (enableNondet)
    {
      throw new RuntimeException(
        "Cannot execute program with CProver.nondetWithNull<T>(T)");
    }
  }

  //  Set a variable to a nondeterminate state, which must NOT be nullptr, but
  //  reference fields of the object may be null.
  public static <T> void nondetWithoutNull(T t)
  {
    if (enableNondet)
    {
      throw new RuntimeException(
        "Cannot execute program with CProver.nondetWithoutNull<T>(T)");
    }
  }

  public static void assume(boolean condition) 
  {
    if(enableAssume)
    {
      throw new RuntimeException(
        "Cannot execute program with CProver.assume()");
    }
  }  
}
