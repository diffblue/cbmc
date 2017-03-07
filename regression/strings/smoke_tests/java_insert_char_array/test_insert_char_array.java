public class test_insert_char_array
{
   public static void main(/*String[] argv*/)
   {
      StringBuilder sb = new StringBuilder("ae");
      char[] array = new char[3];
      array[0] = 'a';
      array[1] = 'b';
      array[2] = 'c';
      sb.insert(1, array);
      String s = sb.toString();
      assert(s.equals("abcde"));
   }
}
