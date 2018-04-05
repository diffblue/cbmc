
public class test3 {

  public static void testme(boolean nondet) {

    // A simple test with a possible exceptional exit.
    try {
      int x = 0;
      float y = 1.0f;
      if(nondet)
        throw new Exception();
    }
    catch(Exception e) {
    }

  }

}
