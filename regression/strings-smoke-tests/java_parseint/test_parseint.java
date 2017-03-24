public class test_parseint
{
   public static void main(String[] argv)
   {
      String twelve = new String("12");
      int parsed = Integer.parseInt(twelve);
      assert(parsed == 12);
      assert(parsed != 12);
   }
}
