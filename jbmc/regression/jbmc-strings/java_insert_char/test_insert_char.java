public class test_insert_char
{
   public static void main()
   {
      StringBuilder sb = new StringBuilder("ac");
      sb.insert(1, 'b');
      String s = sb.toString();
      assert(!s.equals("abc"));
   }
}
