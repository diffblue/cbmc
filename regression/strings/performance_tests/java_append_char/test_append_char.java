public class test_append_char
{
   public static void main(/*String[] args*/)
   {
      char[] diff = {'d', 'i', 'f', 'f'};
      char[] blue = {'b', 'l', 'u', 'e'};

      StringBuilder buffer = new StringBuilder();

      buffer.append(diff)
            .append(blue);

      String tmp=buffer.toString();
      System.out.println(tmp);
      assert(!tmp.equals("diffblue"));
   }
}
