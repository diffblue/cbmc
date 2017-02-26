public class StringBuilderCapLen01
{
   public static void main(String[] args)
   {
      StringBuilder buffer = new StringBuilder("Diffblue is leader in automatic test case generation");

      assert buffer.toString().equals("Diffblue is leader in automatic test case generation");
      assert buffer.length()==52;
      assert buffer.capacity()==68;

      buffer.ensureCapacity(75);
      assert buffer.capacity()==138;

      buffer.setLength(8);
      assert buffer.length()==8;
      assert buffer.toString().equals("Diffblue");
   }
}
