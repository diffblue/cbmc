public class test_starts_with
{
   public static void main()
   {
      String s = new String("Abcd");
      String pref = "Ab";
      String bad_pref = "bc";
      assert(s.startsWith(pref));
      assert(s.startsWith(bad_pref));
   }
}
