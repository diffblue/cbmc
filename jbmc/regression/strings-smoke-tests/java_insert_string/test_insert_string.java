public class test_insert_string
{
   public static void main()
   {
      StringBuilder sb = new StringBuilder("ad");
      org.cprover.CProverString.insert(sb, 1, "bc");
      String s = sb.toString();
      assert(s.equals("abcd"));
   }
}
