public class test_set_length
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder s = new StringBuilder("abc");
      s.setLength(10);
      String t = s.toString();
      assert(t.startsWith("abc"));
      assert(t.length() == 10);
      assert(t.length() == 3);
   }
}
