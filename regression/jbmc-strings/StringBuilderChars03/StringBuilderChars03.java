public class StringBuilderChars03
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("DiffBlue Limited");
      assert buffer.charAt(0)==buffer.charAt(4);
   }
}
