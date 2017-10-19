public class StringBuilderCapLen02
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue is leader in automatic test case generation");
      assert buffer.toString().equals("Diffblue  is leader in automatic test case generation");
   }
}
