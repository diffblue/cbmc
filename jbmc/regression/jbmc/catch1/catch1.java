class some_exception1 extends Throwable
{
};

class some_exception2 extends some_exception1
{
};

class catch1
{
  public static void main(String[] args)
  {
    try
    {
      throw new some_exception2();
    }
    
    catch(some_exception1 e)
    {
    }
  }
}

