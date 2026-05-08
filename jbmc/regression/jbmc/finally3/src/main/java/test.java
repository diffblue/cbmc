public class test {
 public static void main() throws Exception {
   try {
     throw new NullPointerException();
   }
   catch(ArithmeticException e) {
     assert(false);
   }
   finally {
     assert(false);
   }
 }
}

