
public class test {
 public static void main () {
   try {
     int[] array = null;
     int x = array[0];
   }
   catch(NullPointerException e) {
     assert false;
   }
 }
}
