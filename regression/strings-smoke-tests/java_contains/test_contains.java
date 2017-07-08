public class test_contains
{
   public static void main(String x)
   {
      String s = new String("Abc");
      String u = "bc";
      String t = "ab";
      assert(s.contains(u));
      assert(!s.contains(t));

      String z = new String(x);
      if (z.length() > 3) assert(t.contains(z));
      else assert(z.contains(u));
   }
}
