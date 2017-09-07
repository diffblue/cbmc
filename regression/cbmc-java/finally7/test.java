public class test {
 public static void main() throws Exception {
   try {
     f();
   }
   catch(ArithmeticException e) {
     assert(false);
   }
   finally {
     assert(false);
   }
 }

 public static void f() throws NullPointerException {
   throw new NullPointerException();
 }
}

