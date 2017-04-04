public class test_replace
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("abcabd");
      String u = s.replace("d","z");
      System.out.println(u);
      assert(u.equals("abcabz"));
      String v = u.replace("ab","w");
      System.out.println(v);
      assert(v.equals("wcwz"));
   }
}
