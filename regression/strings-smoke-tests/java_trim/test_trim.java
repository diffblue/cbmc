public class test_trim
{
   public static void main(/*String[] argv*/)
   {
      String empty = "   ";
      assert(empty.trim().isEmpty());
      assert(empty.isEmpty());
   }
}
