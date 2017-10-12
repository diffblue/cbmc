public class test_contains
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Abc");
      String u = "bc";
      assert(!s.contains(u));
   }
}
