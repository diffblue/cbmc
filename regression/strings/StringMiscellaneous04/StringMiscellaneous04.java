public class StringMiscellaneous04
{
   public static void main(String[] args)
   {
      String s1 = "diffblue";
      String s2 = "TESTGENERATION";
      String s3 = "   automated   ";

      assert s1.equals("diffblue");
      assert s2.equals("TESTGENERATION");
      assert s3.equals("   automated   ");

      System.out.printf(
         "Replace 'f' with 'F' in s1: %s\n\n", s1.replace('f', 'F'));
      String tmp=s1.replace('f', 'F');
      assert tmp.equals("diFFblue");

      tmp=s1.toUpperCase();
      assert tmp.equals("DIFFBLUE");

      tmp=s2.toLowerCase();
      assert tmp.equals("testgeneration");

      tmp=s3.trim();
      assert tmp.equals("automated");

      // test toCharArray method
      char[] charArray = s1.toCharArray();
      System.out.print("s1 as a character array = ");

      int i=0;
      for (char character : charArray)
      {
         assert character=="diffblue".charAt(i);
         ++i;
      }

      System.out.println();
   }
}
