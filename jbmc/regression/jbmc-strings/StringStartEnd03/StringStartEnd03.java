public class StringStartEnd03
{
   public static void main(String[] args)
   {
      String[] strings = {"tested", "testing", "passed", "passing"};

      int i=0;
      for (String string : strings)
      {
         if (string.endsWith("ed"))
            ++i;
      }
      assert i==3;
   }
}
