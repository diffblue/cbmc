public class test {
 public static void main() throws Exception {
   try {
     int x = 1;
     x++;
   }
   catch(ArithmeticException e) {
     assert(false);
   }
   finally {
     assert(false);
   }
 }
}

