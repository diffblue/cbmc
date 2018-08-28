public class A {

    public void foo(int i ) {
      // We use integer constants that we grep for later in a goto program.
      int x = 1001 + i;
      if (i > 0) {
        x = 1002 + i;
        x = 1003 + i;
        assert false;
      }
      else {
        x = 1004 + i;
        assert false;
      }
      x = 1005 + i;  
    }
}
