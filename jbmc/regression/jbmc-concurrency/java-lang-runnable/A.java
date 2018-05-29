// JBMC, concurrency tests that make use of
// the java.lang.Runnable model

import java.lang.Thread;
import org.cprover.CProver;

public class A
{
  // calling start from outside.
  // expected verfication success.
  public void me3()
  {
    C c = new C();
    Thread tmp = new Thread(c);
    tmp.start();
    c.setX();
  }

  // calling start from outside, no race-condition on B.x
  // expected verfication success.
  public void me4()
  {
    B b = new B();
    Thread tmp = new Thread(b);
    tmp.start();
  }

  // expected verfication failed
  public void me2()
  {
    B b = new B();
    b.me();
  }

  // expected verfication success.
  public void me()
  {
    C c = new C();
    c.me();
  }
}

class B implements Runnable
{
  int x = 0;

  @Override
  public void run()
  {
    x = 44;
    int local_x = x;
    assert(local_x == 44);
  }

  public void me()
  {
    Thread tmp = new Thread(this);
    tmp.start();
    x = 10;
  }
}


class C implements Runnable
{
  int x = 0;

  @Override
  public void run()
  {
    x = 44;
    int local_x = x;
    assert(local_x == 44 || x == 10);
  }

  public void me()
  {
    Thread tmp = new Thread(this);
    tmp.start();
    setX();
  }

  public void setX()
  {
    x = 10;
  }
}
