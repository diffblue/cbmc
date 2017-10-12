public class StringConcatenation04
{
   public static void main(String[] args)
   {
      String s1 = "Happy at";
      String tmp=s1;
      System.out.printf("s1 after concatenation = %s\n", s1);
      assert tmp.equals("Happy  at");
   }
}
