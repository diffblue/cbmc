public class StringValueOf09
{
   public static void main(String[] args)
   {
      double doubleValue = 33.333; // no suffix, double is default
      String tmp=String.valueOf(doubleValue);
      assert tmp.equals("33.3333");
   }
}
