public class StringCompare04
{
   public static void main(String[] args)
   {
      String s1 = new String("test");
      String s2 = "goodbye";
      assert s2.compareTo(s1)==13; //false
   }
}
