import java.lang.Thread;
import org.cprover.CProver;

public class A
{
  int x = 0;

  // expected verfication success
  public void me()
  {
    Thread t = new Thread()
    {
      public void run()
      {
        x = 44;
        int local_x = x;
        assert(local_x == 44 || x == 10);
      }
    };
    t.start();
    x = 10;
  }

  // expected verfication failure
  public void me2()
  {
    Thread t = new Thread()
    {
      public void run()
      {
        x = 44;
        int local_x = x;
        assert(local_x == 44);
      }
    };
    t.start();
    x = 10;
  }
}
