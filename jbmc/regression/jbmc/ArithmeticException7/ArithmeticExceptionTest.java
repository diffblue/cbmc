public class ArithmeticExceptionTest {
    public static void  main(String args[]) {
        try {
            int i=0;
            int j=10/i;
        }
        catch(Exception exc) {
            assert false;
        }
    }
}
