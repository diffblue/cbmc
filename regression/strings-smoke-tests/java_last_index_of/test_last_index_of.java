public class test_last_index_of
{
   public static void main(/*String[] argv*/)
   {
      String s = "abcab";
      String ab = "ab";
      int i = s.lastIndexOf(ab);
      assert(i == 3);
   }
}
