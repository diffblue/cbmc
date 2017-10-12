public class StringMiscellaneous03
{
   public static void main(String[] args)
   {
      String s1 = "Automatic Test Generation";
      String s2 = "noitareneG tseT citamotuA";
      char[] charArray = new char[5];
      int i=0;
      for (int count = s1.length() - 1; count >= 0; count--)
      {
         assert s1.charAt(count) != s2.charAt(i);
         ++i;
      }
   }
}
