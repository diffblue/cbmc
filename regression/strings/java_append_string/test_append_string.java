public class test_append_string
{
   public static void main(/*String[] args*/)
   {
      String di = new String("di");
      StringBuilder diff = new StringBuilder();
      diff.append(di);
      diff.append("ff");
      System.out.println(diff);
      String s = diff.toString();
      System.out.println(s);
      assert (!s.equals("diff"));
   }
}
