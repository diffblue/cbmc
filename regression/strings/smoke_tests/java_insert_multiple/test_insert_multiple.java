public class test_insert_multiple
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder sb = new StringBuilder("ae");
      sb.insert(1, 'b');
      sb.insert(1, "cd");
      String s = sb.toString();
      assert(s.equals("abcde"));
   }
}
