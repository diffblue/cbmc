public class test_append_int
{
   public static void main(/*String[] args*/)
   {
      StringBuilder diffblue = new StringBuilder();
      diffblue.append("d");
      diffblue.append(4);
      String s = diffblue.toString();
      assert s.equals("d4");
   }
}
