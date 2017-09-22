public class test
{
   public static void main(String[] args)
   {
      StringBuilder sb = new StringBuilder(args[0]);
      sb.append("Z");
      String s = sb.toString();
      assert(s.equals("fg"));
   }
}
