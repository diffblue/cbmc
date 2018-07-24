import java.io.*;

public class ThrowsExceptions {

  public static void test() throws CustomException, IOException {
     StringReader sr = new StringReader("");
     sr.read();
     throw new CustomException();
  }

}

class CustomException extends Exception {
}
