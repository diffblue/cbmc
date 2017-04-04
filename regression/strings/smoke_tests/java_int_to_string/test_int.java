public class test_int
{
   public static void main(/*String[] argv*/)
   {
      String s = Integer.toString(12);
      assert(s.equals("12"));
      String t = Integer.toString(-23);
      System.out.println(t);
      assert(t.equals("-23"));
   }
}
