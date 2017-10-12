public class StringBuilderCapLen03
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue is leader in automatic test case generation");
      assert buffer.length()==51;
   }
}
