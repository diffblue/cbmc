public class test {
 public static void main() throws Exception {
   try {
     f();
   }
   finally {
     assert(false);
   }
 }

 public static void f() throws Exception {
   throw new Exception();
 }
}

