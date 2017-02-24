public class test_set_char_at
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Abc");
      char c = s.charAt(1);
      StringBuilder sb = new StringBuilder(s);
      sb.setCharAt(1,'w');
      s = sb.toString();
      assert(s.equals("Awc"));
      assert(s.charAt(2)=='c');
   }
}
