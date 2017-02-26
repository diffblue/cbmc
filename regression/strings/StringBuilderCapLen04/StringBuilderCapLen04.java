public class StringBuilderCapLen04
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue is leader in automatic test case generation");
      assert buffer.capacity()==69;
   }
}
