public class test_endswith
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Abcd");
      String suff = "cd";
      assert(!s.endsWith(suff));
   }
}
