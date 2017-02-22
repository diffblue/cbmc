public class StringBuilderConstructors01
{
   public static void main(String[] args)
   {
      StringBuilder buffer1 = new StringBuilder();
      StringBuilder buffer2 = new StringBuilder(10);
      StringBuilder buffer3 = new StringBuilder("diffblue");

      assert buffer1.length()==0;
      assert buffer2.length()==0;
      assert buffer3.length()>0;
   }
}
