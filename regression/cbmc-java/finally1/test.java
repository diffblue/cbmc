public class test {
 public static void main() throws Exception {
   try {
     throw new Exception();
   }
   finally {
     assert(false);
   }
 }
}

