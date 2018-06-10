public class test_index_of_char
{
   public static void main()
   {
      String s = "Abc";
      char c = 'c';
      int i = s.indexOf(c);
      assert(i == 2);
   }
}
