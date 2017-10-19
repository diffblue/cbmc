public class test_delete
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder s = new StringBuilder("Abc");
      s.delete(1,2);
      String str = s.toString();
      assert(!str.equals("Ac"));
   }
}
