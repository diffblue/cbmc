public class test_insert_char
{
   public static void main()
   {
      StringBuilder sb = new StringBuilder("ac");
      org.cprover.CProverString.insert(sb, 1, 'b');
      String s = sb.toString();
      assert(s.equals("abc"));
   }
}
