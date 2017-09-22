public class test_insert_string
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder sb = new StringBuilder("ad");
      sb.insert(1, "bc");
      String s = sb.toString();
      assert(!s.equals("abcd"));
   }
}
