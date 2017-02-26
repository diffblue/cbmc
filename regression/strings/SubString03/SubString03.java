public class SubString03
{
   public static void main(String[] args)
   {
      String letters = "automatictestcasegenerationatdiffblue";
      String tmp=letters.substring(9, 13);
      assert tmp.equals("teest");
   }
}
