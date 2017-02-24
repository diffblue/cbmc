public class test_case
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Ab");
      String l = s.toLowerCase();
      String u = s.toUpperCase();
      assert(l.equals("ab"));
      assert(u.equals("AB"));
      assert(s.equalsIgnoreCase("aB"));
   }
}
