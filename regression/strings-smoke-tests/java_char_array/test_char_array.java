public class test_char_array
{
   public static void main(int i)
   {
      String s = "abc";
      char [] str = s.toCharArray();
      char c = str[2];
      char a = s.charAt(0);
      assert(str.length == 3);
      assert(a == 'a');
      assert(c == 'c');
      if(i==0)
          assert(str.length != 3);
      if(i==2)
          assert(a != 'a');
      if(i==3)
          assert(c != 'c');
   }
}
