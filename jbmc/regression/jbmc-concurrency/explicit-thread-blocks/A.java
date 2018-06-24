import java.lang.Thread;
import org.cprover.CProver;

public class A
{
  static int x = 0;

  // verification success
  public void me()
  {
    x = 5;
    CProver.startThread(333);
    x = 10;
    CProver.endThread(333);
    assert(x == 5 || x == 10);
  }

  // verification failed
  public void me2()
  {
    x = 5;
    CProver.startThread(333);
    x = 10;
    CProver.endThread(333);
    assert(x == 10);
  }

  // Known-bug, thread id mismatch, this should be detected by the conversation
  // process. It is currently not and thus will result in an assertion violation
  // during symbolic execution.
  public void me3()
  {
    x = 5;
    CProver.startThread(22333);
    x = 10;
    CProver.endThread(333);
    assert(x == 10);
  }

  // Known-bug, see: https://github.com/diffblue/cbmc/issues/1630
  public void me4()
  {
    int x2 = 10;
    CProver.startThread(22333);
    x = x2;
    assert(x == 10);
    CProver.endThread(333);
  }

  // Known-bug, symex cannot handle nested thread-blocks
  public void me5()
  {
    CProver.startThread(333);
    x = 5;
    CProver.startThread(222);
    x = 8;
    CProver.endThread(222);
    CProver.endThread(333);
    assert(x == 5 || x == 0 || x == 8);
  }
}
