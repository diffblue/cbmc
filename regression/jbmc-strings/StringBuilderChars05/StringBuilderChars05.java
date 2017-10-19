public class StringBuilderChars05
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue Limited");
      buffer.setCharAt(0, 'H');
      buffer.setCharAt(6, 'T');
      assert buffer.toString().equals("HiffBllTe Limited");
   }
}
