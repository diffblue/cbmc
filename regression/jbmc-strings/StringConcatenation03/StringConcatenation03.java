public class StringConcatenation03
{
   public static void main(String[] args)
   {
      String s1 = "Happy at";
      String s2 = " Diffblue";

      System.out.printf(
         "Result of s1.concat(s2) = %s\n", s1.concat(s2));
      String tmp=s1.concat(s2);
      assert tmp.equals("Happy at DiffBllue");

      tmp=s1;
      System.out.printf("s1 after concatenation = %s\n", s1);
      assert tmp.equals("Happy at");
   }
}
