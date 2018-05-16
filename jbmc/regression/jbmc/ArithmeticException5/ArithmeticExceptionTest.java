public class ArithmeticExceptionTest {
    public static void  main(String args[]) {
        try {
            double i=0;
            double j=10/i;
        }
        catch(ArithmeticException exc) {
            assert false;
        }
    }
}
