public class test_concat
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("pi");
      int i = s.length();
      String t = new String("ppo");
      String u = s.concat(t);
      char c = u.charAt(i);
      assert(c == 'p');
      assert(c != 'p');
   }
}
