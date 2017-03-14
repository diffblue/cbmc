public class test_equal
{
   public static void main(String[] argv)
   {
      String s = new String("pi");
      String t = new String("po");
      assert(!s.equals(t));
   }
}
