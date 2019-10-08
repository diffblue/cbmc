public class StringBuilderChars01
{
   public static void test(boolean choice)
   {
      String s = choice ? "Diffblue" : "abcdefgh";
      StringBuilder buffer = new StringBuilder(s);
	  
      assert !choice || buffer.toString().equals("Diffblue");
      assert buffer.charAt(0)!=buffer.charAt(4);

      char[] charArray = new char[buffer.length()];
      buffer.getChars(0, buffer.length(), charArray, 0);

      int i=0;
      for (char character : charArray)
      {
         System.out.print(character);
         assert character==buffer.charAt(i);
         ++i;
      }

      buffer.setCharAt(0, 'H');
      buffer.setCharAt(6, 'T');
      assert !choice || buffer.toString().equals("HiffblTe");

      buffer.reverse();
      assert !choice || buffer.toString().equals("eTlbffiH");
   }
}
