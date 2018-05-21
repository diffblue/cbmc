public class ArithmeticExceptionTest {
    public static void  main(int denom) {
        try {
            int j=10/denom;
        }
        catch(ArithmeticException exc) {
            assert false;
        }
    }
}
