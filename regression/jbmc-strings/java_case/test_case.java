public class test_case
{
   public static void main(/*String[] argv*/)
   {
      String s = new String("Ab");
      String l = s.toLowerCase();
      String u = s.toUpperCase();
      assert(!l.equals("ab") ||
             !u.equals("AB") ||
             !s.equalsIgnoreCase("aB"));
   }
}
