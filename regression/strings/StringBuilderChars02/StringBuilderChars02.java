public class StringBuilderChars02
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("DiffBlue Limited");
      assert buffer.toString().equals("DiffBlue Limitted");
   }
}
