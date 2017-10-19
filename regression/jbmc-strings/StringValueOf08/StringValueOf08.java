public class StringValueOf08
{
   public static void main(String[] args)
   {
      float floatValue = 2.5f;
      String tmp=String.valueOf(floatValue);
      assert tmp.equals("2.50");
   }
}
