public class StringBuilderChars05
{
   public static void test(boolean choice)
   {
      String s = choice ? "Diffblue Limited" : "Diffblue Unlimited";
      StringBuilder buffer = new StringBuilder(s);
      buffer.setCharAt(0, 'H');
      buffer.setCharAt(6, 'T');
      assert !choice || buffer.toString().equals("HiffBllTe Limited");
   }
}
