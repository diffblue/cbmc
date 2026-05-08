class MyException extends Exception {}

// This test verifies that we can handle the exception table not being ordered
public class test {
    public static void main(String args[]) throws Exception {
        try {
            int x = 5;
            try {
                if (args.length == 0)
                    return;
                if (args.length == 1)
                    throw new MyException();
            } catch(Exception ex) {
                assert(false);
                throw ex;
            }
        } catch(MyException ex) {
        }
    }
}
