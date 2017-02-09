package org.cprover;

public final class CProver
{
  public static boolean enableAssume=true;
  public static void assume(boolean condition) 
  {
    if(enableAssume)
      throw new RuntimeException("Cannot execute program with CProver.assume()");
  }  
}
