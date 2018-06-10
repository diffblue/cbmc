public class test_delete
{
   public static void main()
   {
      StringBuilder s = new StringBuilder("Abc");
      org.cprover.CProverString.delete(s,1,2);
      String str = s.toString();
      assert(!str.equals("Ac"));
   }
}
