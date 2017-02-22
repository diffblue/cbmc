public class StringCompare03
{
   public static void main(String[] args)
   {
      String s3 = "Automatic Test Generation";
      String s4 = "automatic test generation";

      // test regionMatches (ignore case)
      if (!s3.regionMatches(true, 0, s4, 0, 5)) //false
         assert true;
      else
         assert false;
   }
}
