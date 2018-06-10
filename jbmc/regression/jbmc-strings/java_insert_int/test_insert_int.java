public class test_insert_int
{
   public static void main()
   {
      StringBuilder sb = new StringBuilder("ac");
      org.cprover.CProverString.insert(sb, 1, 42);
      String s = sb.toString();
      assert(!s.equals("a42c"));
   }
}
