public class StringIndexMethods01
{
   public static void main(String[] args)
   {
      String letters = "automatictestcasegenerationatdiffblue";

      assert letters.indexOf('c')==8;
      assert letters.indexOf('a', 1)==5;
      assert letters.indexOf('$')==-1;
      assert letters.lastIndexOf('c')==13;
      assert letters.lastIndexOf('a', 25)==22;
      assert letters.lastIndexOf('$')==-1;
      assert letters.indexOf("diffblue")==29;
      assert letters.indexOf("diffblue", 7)==29;
      assert letters.indexOf("generation")==17;
      assert letters.lastIndexOf("diffblue")==29;
      assert letters.lastIndexOf("diffblue", 25)==-1;
      assert letters.lastIndexOf("automatic")==0;
   }
}
