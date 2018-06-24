import java.lang.Thread;
import org.cprover.CProver;

public class A
{
  // expected verification success
  public static void me()
  {
    B b = new B();
    b.me();
  }

  // expected verification failure
  public static void me2()
  {
    C c = new C();
    c.me();
  }

  // Create 2 Threads, no shared variables
  // expected verification success
  //
  // FIXME: attempting to create more threads will
  // currently result in an exponential blow-up
  // in the  number of clauses.
  public void me3()
  {
    for(int i = 0; i<2; i++)
    {
       D d = new D();
       d.start();
       d.setX();
    }
  }
}

class D extends Thread
{
  int x = 0;

  @Override
  public void run()
  {
    x = 44;
    int local_x = x;
    assert(local_x == 44 || local_x == 10);
  }
  public void setX()
  {
    x = 10;
  }
}

class B implements Runnable
{
  // FIXME: this assertion does not always hold as per the java spec (because x
  // is not volatile), but cbmc currently doesn't reason about java volatile
  // variables
  int x = 0;
  @Override
  public void run()
  {
    x += 1;
    int local_x = x;
    assert(local_x == 1 || local_x == 2 ||
      local_x == 10 || local_x == 11 || local_x == 12);
  }

  // verification success
  public void me()
  {
    Thread t1 = new Thread(this);
    t1.start();
    Thread t2 = new Thread(this);
    t2.start();
    x = 10;
  }
}

class C implements Runnable
{
  int x = 0;

  @Override
  public void run()
  {
    x += 1;
    int local_x = x;
    assert(local_x == 1 || local_x == 2);
  }

  // verification fails because the assertion does not account for the writes of
  // this thread
  public void me()
  {
    Thread t1 = new Thread(this);
    t1.start();
    Thread t2 = new Thread(this);
    t2.start();
    x = 10;
  }
}
