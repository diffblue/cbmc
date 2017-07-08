public class test_int
{
   public static void main(int i)
   {
      String s = Integer.toString(12);
      assert(s.equals("12"));
      String t = Integer.toString(-23);
      System.out.println(t);
      assert(t.equals("-23"));
      if(i==1)
          assert(!s.equals("12"));
      else if(i==2)
          assert(!t.equals("-23"));
   }
}
