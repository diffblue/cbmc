public class test_last_index_of_char
{
   public static void main(/*String[] argv*/)
   {
      String s = "abcab";
      int n = s.lastIndexOf('a');
      assert(n == 3);
   }
}
