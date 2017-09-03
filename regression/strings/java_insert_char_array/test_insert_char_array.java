public class test_insert_char_array
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder sb = new StringBuilder("ad");
      char[] array = new char[2];
      array[0] = 'b';
      array[1] = 'c';
      sb.insert(1, array);
      String s = sb.toString();
      System.out.println(s);
      assert(!s.equals("abcd"));
   }
}
