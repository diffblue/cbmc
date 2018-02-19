public class test_insert_multiple
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder sb = new StringBuilder("ad");
      org.cprover.CProverString.insert(sb, 1, 'c');
      org.cprover.CProverString.insert(sb, 1, "b");
      String s = sb.toString();
      assert(s.equals("abcd"));
   }
}
