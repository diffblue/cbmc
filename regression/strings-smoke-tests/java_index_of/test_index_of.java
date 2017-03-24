public class test_index_of
{
   public static void main(/*String[] argv*/)
   {
      String s = "Abc";
      String bc = "bc";
      int i = s.indexOf(bc);
      assert(i == 1);
   }
}
