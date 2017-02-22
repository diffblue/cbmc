public class StringValueOf04
{
   public static void main(String[] args)
   {
      boolean booleanValue = false;
      String tmp=String.valueOf(booleanValue);
      assert tmp.equals("true");
   }
}
