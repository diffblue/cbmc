public class test_replace_char
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("abcabd");
      String t = s.replace('b','m');
      assert(t.equals("amcamd"));
   }
}
