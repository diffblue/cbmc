import java.lang.RuntimeException;
import org.cprover.CProver;

public class Sync
{
  public int field;

  public static void main(String[] args)
  {
    final Sync o = new Sync();
    o.field = 0;
    // test regular synchronized method (monitorexit on return)
    o.f();
    // test synchronized method with throw (monitorexit on catch)
    try
    {
      o.g();
    }
    catch (RuntimeException e)
    {
      o.field++;
    }
    // Make sure both functions were executed and the second threw
    // The object should remain unlocked
    if ((o.field !=3) || (CProver.getMonitorCount(o) !=0))
      assert(false);
  }

  public synchronized void f()
  {
    // Check that we acquired  the lock
    if (CProver.getMonitorCount(this) !=1)
      assert(false);
    field++;
  }

  public synchronized void g()
  {
    field++;
    // Check that we acquired  the lock
    if (CProver.getMonitorCount(this) !=1)
      assert(false);
    throw new RuntimeException();
  }
}
