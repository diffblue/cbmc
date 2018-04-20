public class StringConcatenation01
{
   public static void main(String[] args)
   {
      String s1 = "Happy at";
      String s2 = " Diffblue";

      assert s1.equals("Happy at");
      assert s2.equals(" Diffblue");

      String tmp=s1.concat(s2);
      assert tmp.equals("Happy at Diffblue");

      tmp=s1;
      assert tmp.equals("Happy at");
   }
}
