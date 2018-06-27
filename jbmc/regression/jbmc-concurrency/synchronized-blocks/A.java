public class A
{
  public void me0()
  {
    final Object o = new Object();
    try
    {
      synchronized (o) {}
    }
    catch (NullPointerException e)
    {
      assert false;
      return;
    }
  }

  // expected verification success
  public static void aStatic() throws java.io.IOException
  {
    Object _lock = new Object();
    try
    {
      synchronized (_lock)
      {
        if(true)
          throw new java.io.IOException();
      }
    }
    catch (java.io.IOException e)
    {
      return;
    }
    assert false; // unreachable
  }

  // expected verification success
  // --
  // base-case, no synchronization
  public void me1()
  {
    B t = new B();
    t.shared = 5;
    t.start();
    assert(t.shared == 5 || t.shared == 6);
  }

  // expected verification success
  // --
  // locking mechanism
  public void me2()
  {
    B t = new B();
    synchronized(t.lock)
    {
      t.shared = 5;
      t.start();
      assert(t.shared == 5);
    }
  }
}

class B extends Thread
{
  public Object lock = new Object();
  public int shared = 0;

  @Override
  public void run()
  {
    set();
  }
  public void set()
  {
    synchronized(lock)
    {
      shared++;
    }
  }
}
