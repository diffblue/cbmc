class some_exception1 extends Throwable
{
};

class some_exception2 extends some_exception1
{
};

class catch1
{
  public static void catchSuper() throws Throwable
  {
    try
    {
      throw new some_exception2();
    }
    
    catch(some_exception1 e)
    {
    }
  }

  public static void catchSub() throws Throwable
  {
    try
    {
      throw new some_exception1();
    }

    catch(some_exception2 e)
    {
    }
  }
}

