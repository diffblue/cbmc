public class test_delete_char_at
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder s = new StringBuilder();
      s.append("Abc");
      s.deleteCharAt(1);
      String str = s.toString();
      assert(!str.equals("Ac"));
   }
}
