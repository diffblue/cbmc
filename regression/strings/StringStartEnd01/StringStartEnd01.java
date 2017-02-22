public class StringStartEnd01
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
      assert i==2;

      i=0;	
      for (String string : strings)
      {
         if (string.startsWith("ste", 2))
           ++i;
      }
      assert i==1;

      i=0;
      for (String string : strings)
      {
         if (string.endsWith("ed"))
            ++i;
      }
      assert i==2;
   }
}
