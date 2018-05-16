public class test {
 public static void main() throws Exception {
   try {
     throw new Exception();
   }
   catch(Exception e) { }
   finally {
     assert(false);
   }
 }
}

