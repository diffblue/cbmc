public class A
{
  static int g;

  public synchronized void me1()
  {
    g = 0;
  }

  // expected verification success
  // --
  // base-case, no synchronization
  public void me2()
  {
    B t = new B();
    t.shared = 5;
    t.start();
    assert(t.shared == 5 || t.shared == 6);
  }

  // expected verification success
  // --
  // locking mechanism
  public void me3()
  {
    B t = new B();
    synchronized(t)
    {
      t.shared = 5;
      t.start();
      assert(t.shared == 5);
    }
  }

  // expected verification success
  // --
  // KNOWNBUG: synchronization of static synchronized
  // methods is not yet supported
  public void me4()
  {
    C t = new C();
    synchronized(C.class)
    {
      C.shared = 5;
      t.start();
      assert(C.shared == 5);
    }
  }
}

class B extends Thread
{
  public int shared = 0;

  @Override
  public void run()
  {
    set();
  }
  public synchronized void set()
  {
    shared++;
  }
}

class C extends Thread
{
  public static int shared = 0;

  @Override
  public void run()
  {
    C.static_set();
  }

  public static synchronized void static_set()
  {
    C.shared++;
  }
}
