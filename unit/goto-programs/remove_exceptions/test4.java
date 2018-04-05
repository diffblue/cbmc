
public class test4 {

  public static void testme(int nondet) {

    // Two possible exceptional exits, which should share an exit sequence.
    try {
      int x = 0;
      float y = 1.0f;
      if(nondet == 1)
        throw new Exception("Exn1");
      else if(nondet == 2)
        throw new Exception("Exn2");
    }
    catch(Exception e) {
    }

  }

}
