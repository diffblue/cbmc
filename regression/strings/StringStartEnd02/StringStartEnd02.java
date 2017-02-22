public class StringStartEnd02
{
   public static void main(String[] args)
   {
      String[] strings = {"tested", "testing", "passed", "passing"};

      int i=0;
      for (String string : strings)
      {
         if (string.startsWith("te"))
            ++i;
      }
      assert i==1;
   }
}
