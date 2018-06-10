public class test_trim
{
   public static void main()
   {
      String empty = "   ";
      assert(empty.trim().isEmpty());
      assert(empty.isEmpty());
   }
}
