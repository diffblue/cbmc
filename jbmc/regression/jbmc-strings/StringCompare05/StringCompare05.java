public class StringCompare05
{
   public static void main(String[] args)
   {
      String s1 = new String("test");
      if (s1 == "test")  // false; they are not the same object
         assert true;
      else
         assert false;
   }
}
