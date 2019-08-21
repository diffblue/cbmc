public class test_insert_multiple
{
   public static void main()
   {
      StringBuilder sb = new StringBuilder("ad");
      sb.insert(1, 'c');
      sb.insert(1, "b");
      String s = sb.toString();
      assert(s.equals("abcd"));
   }
}
