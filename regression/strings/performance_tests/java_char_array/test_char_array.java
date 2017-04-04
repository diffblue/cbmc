public class test_char_array
{
   public static void main(/*String[] argv*/)
   {
      String s = "abc";
      char [] str = s.toCharArray();
      char c = str[2];
      char a = s.charAt(0);
      assert(str.length != 3 ||
             a != 'a' ||
             c != 'c');
   }
}
