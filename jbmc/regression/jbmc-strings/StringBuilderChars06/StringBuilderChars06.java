public class StringBuilderChars06
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue Limited");
      buffer.reverse();
      assert buffer.toString().equals("detimiL eTlBffiiH");
   }
}
