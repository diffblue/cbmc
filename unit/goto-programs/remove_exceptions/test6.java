
public class test6 {

  public static void testme(int nondet, boolean nondet2) {

    // Two possible exceptional exits, which should share an exit sequence,
    // each leading to two possible targets, plus the complication that
    // there are nested try-blocks to escape from.
    try {
      int x = 0;
      try {
        float y = 1.0f;
        Throwable maybe_exception = nondet2 ? new Exception("Exn1") : new Throwable();
        if(nondet == 1)
          throw maybe_exception;
        else if(nondet == 2)
          throw maybe_exception;
      }
      catch(Exception e) {
      }
    }
    catch(Throwable e) {
    }

  }

}
