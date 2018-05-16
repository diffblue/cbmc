public class StringIndexMethods04
{
   public static void main(String[] args)
   {
      String letters = "onatdiffblue";
      assert letters.indexOf("diffblue")==2;
   }

  public static void mainBug(String[] args)
   {
      String letters = "automatictestcasegenerationatdiffblue";
      assert letters.indexOf("diffblue")==28;
   }
}
