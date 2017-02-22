public class StringCompare02
{
   public static void main(String[] args)
   {
      String s3 = "Automatic Test Generation";
      String s4 = "automatic test generation";

      // test regionMatches (case sensitive)
      if (s3.regionMatches(0, s4, 0, 5)) //false
         assert true;
      else
         assert false;
   }
}
