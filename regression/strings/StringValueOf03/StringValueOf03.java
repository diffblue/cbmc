public class StringValueOf03
{
   public static void main(String[] args)
   {
      char[] charArray = {'d', 'i', 'f', 'f', 'b', 'l', 'u', 'e'};
      String tmp=String.valueOf(charArray, 3, 3);
      assert tmp.equals("fbbl");
   }
}
