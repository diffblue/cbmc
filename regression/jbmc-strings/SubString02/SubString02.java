public class SubString02
{
   public static void main(String[] args)
   {
      String letters = "automatictestcasegenerationatdiffblue";
      String tmp=letters.substring(20);
      assert tmp.equals("erationatdifffblue");
   }
}
