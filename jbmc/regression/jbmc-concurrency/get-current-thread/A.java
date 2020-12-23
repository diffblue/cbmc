import java.lang.Thread;
import org.cprover.CProver;

public class A
{
  public static int g;

  // expected verification success
  public void me()
  {
    int g = CProver.getCurrentThreadId();
    assert(g == 0);
  }

  // expected verification success
  // --
  // KNOWNBUG
  // ---
  // For some reason symex assigns 'g' to zero, even though
  // the only viable assignment should be one.
  // This issue seems to only occur when a variable is
  // assigned inside the local scope of a thread-block.
  //
  // If instead, we call a function from inside the thread-block and
  // then assign  'g' to 1 then as expected the only viable
  // assignment to 'g' is 1 (see 'me4')
  //
  // Seems related to: https://github.com/diffblue/cbmc/issues/1630/
  public void me_bug()
  {
    CProver.startThread(333);
    int g = 1;
    assert(g == 1);
    CProver.endThread(333);
  }

  // expected verification success
  // --
  // KNOWNBUG: see me_bug()
  public void me2()
  {
    CProver.startThread(333);
    g = CProver.getCurrentThreadId();
    assert(g == 1);
    CProver.endThread(333);
  }

  // expected verification success
  // --
  // KNOWNBUG: see me_bug()
  public void me3()
  {
    CProver.startThread(333);
    int i = CProver.getCurrentThreadId();
    assert(g == 1);
    CProver.endThread(333);
  }

  // expected verification success.
  public void me4()
  {
    CProver.startThread(333);
    check();
    CProver.endThread(333);
  }

  // expected verification success.
  public void me5()
  {
    me();
    B b = new B();
    Thread tmp = new Thread(b);
    tmp.start();
  }

  // expected verification success.
  public void me6()
  {
    me();
    C c = new C();
    c.start();
  }

  public void check()
  {
    g = CProver.getCurrentThreadId();
    assert(g == 1);
  }
}

class B implements Runnable
{
  public static int g;
  @Override
  public void run()
  {
    g = CProver.getCurrentThreadId();
    assert(g == 1);
  }
}


class C extends Thread
{
  public static int g;
  @Override
  public void run()
  {
    g = CProver.getCurrentThreadId();
    assert(g == 1);
  }
}
