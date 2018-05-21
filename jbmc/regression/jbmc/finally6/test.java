public class test {
 public static void main() throws Exception {
   try {
     f();
   }
   catch(Exception e) { }
   finally {
     assert(false);
   }
 }

 public static void f() throws Exception {
   throw new Exception();
 }
}

