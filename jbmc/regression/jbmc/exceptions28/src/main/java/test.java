class MyException extends Exception {}

// This test verifies that we can handle the exception table not being ordered
public class test {
  public static void main(String args[]) throws Exception {
    try {
        if (args.length == 1)
            return;
        throw new Exception();
    } catch(MyException ex) {
        throw ex;
    } catch(Exception ex) {
        throw ex;
    }
  }
}
