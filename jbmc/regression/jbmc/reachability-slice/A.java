public class A {

    public void foo(int i ) {
      // We use integer constants that we grep for later in a goto program.
      int x = 1001 + i;
      if (i > 0) {
        x = 1002 + i; // property "java::A.foo:(I)V.coverage.3", see https://github.com/diffblue/cbmc/pull/1943#discussion_r175367063 for a discusison.
        x = 1003 + i;
      }
      else
        x = 1004 + i;
      x = 1005 + i;  
    }
}
