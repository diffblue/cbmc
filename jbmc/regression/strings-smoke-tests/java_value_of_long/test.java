public class test
{
   public static void main(int i)
   {
      long l1=12345678901234L;
      if(i == 0)
      {
          String s = String.valueOf(l1);
          assert(s.equals("12345678901234"));
      }
      else
      {
          String s = String.valueOf(-l1);
          assert(!s.equals("-12345678901234"));
      }
   }
}
