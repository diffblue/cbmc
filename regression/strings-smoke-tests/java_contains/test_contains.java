public class test_contains
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Abc");
      String u = "bc";
      String t = "ab";
      assert(s.contains(u));
      assert(s.contains(t));
   }
}
