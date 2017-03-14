public class test_append_object
{
   public static void main(/*String[] args*/)
   {
      Object diff = "diff";
      Object blue = "blue";

      StringBuilder buffer = new StringBuilder();

      buffer.append(diff)
            .append(blue);

      String tmp=buffer.toString();
      System.out.println(tmp);
      assert tmp.equals("diffblue");
   }
}
