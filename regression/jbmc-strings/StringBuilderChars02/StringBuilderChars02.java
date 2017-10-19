public class StringBuilderChars02
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue Limited");
      assert buffer.toString().equals("Diffblue Limitted");
   }
}
