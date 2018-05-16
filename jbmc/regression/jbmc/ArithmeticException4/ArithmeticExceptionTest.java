public class ArithmeticExceptionTest {
    public static void  main(String args[]) {
        try {
          long denom=0;
          long num=10;
          long result=num%denom;
        }
        catch(ArithmeticException exc) {
            assert false;
        }
    }
}
