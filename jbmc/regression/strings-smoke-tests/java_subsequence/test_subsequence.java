public class test_subsequence
{
   public static void main()
   {
      String abcdef = "AbcDef";
      CharSequence cde = org.cprover.CProverString.subSequence(abcdef,2,5);
      char c = cde.charAt(0);
      char d = cde.charAt(1);
      char e = cde.charAt(2);
      assert(c == 'c');
      assert(d == 'D');
      assert(e == 'e');
  }
}
