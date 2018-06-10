public class test_set_char_at
{
   public static void main()
   {
      String s = new String("Abc");
      char c = org.cprover.CProverString.charAt(s, 1);
      StringBuilder sb = new StringBuilder(s);
      sb.setCharAt(1,'w');
      s = sb.toString();
      assert(s.equals("Awc"));
      assert(org.cprover.CProverString.charAt(s, 2)=='c');
   }
}
