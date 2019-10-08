public class test_set_length
{
   public static void main(boolean choice)
   {
      String s = choice ? "abc" : "abcxyz";
      StringBuilder sb = new StringBuilder(s);
      sb.setLength(10);
      String t = sb.toString();
      assert(t.startsWith("abc"));
      assert(t.length() == 10);
      assert(t.length() == 3);
   }
}
