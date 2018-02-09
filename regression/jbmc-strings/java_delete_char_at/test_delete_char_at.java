public class test_delete_char_at
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder s = new StringBuilder();
      s.append("Abc");
      org.cprover.CProverString.deleteCharAt(s, 1);
      String str = s.toString();
      assert(!str.equals("Ac"));
   }
}
