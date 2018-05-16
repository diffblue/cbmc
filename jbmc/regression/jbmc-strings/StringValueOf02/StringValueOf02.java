public class StringValueOf02
{
   public static void main(String[] args)
   {
      char[] charArray = {'d', 'i', 'f', 'f', 'b', 'l', 'u', 'e'};
      String tmp=String.valueOf(charArray);
      assert tmp.equals("difffblue");
   }
}
