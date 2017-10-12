public class StringConcatenation01
{
   public static void main(String[] args)
   {
      String s1 = "Happy at";
      String s2 = " DiffBlue";

      assert s1.equals("Happy at");
      assert s2.equals(" DiffBlue");

      String tmp=s1.concat(s2);
      assert tmp.equals("Happy at DiffBlue");

      tmp=s1;
      assert tmp.equals("Happy at");
   }
}
