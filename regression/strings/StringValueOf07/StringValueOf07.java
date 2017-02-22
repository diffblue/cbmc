public class StringValueOf07
{
   public static void main(String[] args)
   {
      long longValue = 10000000000L;
      System.out.printf("long = %s\n", String.valueOf(longValue));
      String tmp=String.valueOf(longValue);
      assert tmp.equals("100000000000");
   }
}
