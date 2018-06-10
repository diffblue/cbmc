public class test_endswith
{
   public static void main()
   {
      String s = new String("Abcd");
      String suff = "cd";
      String bad_suff = "bc";

      assert(s.endsWith(suff));
      assert(s.endsWith(bad_suff));
   }
}
