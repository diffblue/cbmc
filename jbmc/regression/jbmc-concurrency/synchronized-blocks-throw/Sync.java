import org.cprover.CProver;

public class Sync
{
  int field;
  public static void main(String[] args)
  {
    Sync o = new Sync();
    try
    {
      o.field=0;
      synchronized (o)
      {
        // Make sure the monitor is taken.
        assert(CProver.getMonitorCount(o) == 1);
        if (CProver.nondetBoolean())
          throw new RuntimeException();
        o.field++;
      }
    }
    catch(RuntimeException e)
    {
      o.field++;
    }
    catch(Throwable e)
    {}

    // Make sure we did not execute in an unexpected way.
    if (o.field != 1)
      assert false;

    // Make sure the monitor is free.
    assert(CProver.getMonitorCount(o) == 0);
  }
}
