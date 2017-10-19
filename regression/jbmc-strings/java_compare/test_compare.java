public class test_compare
{
   public static void main(/*String[] argv*/)
   {
      String s1 = "ab";
      String s2 = "aa";
      assert(s1.compareTo(s2) != 1);
   }
}
