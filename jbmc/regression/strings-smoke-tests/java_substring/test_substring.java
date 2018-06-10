public class test_substring
{
   public static void main()
   {
      String abcdef = "AbcDef";
      String cde = org.cprover.CProverString.substring(abcdef, 2,5);
      char c = org.cprover.CProverString.charAt(cde, 0);
      char d = org.cprover.CProverString.charAt(cde, 1);
      char e = org.cprover.CProverString.charAt(cde, 2);
      assert(c == 'c');
      assert(d == 'D');
      assert(e == 'e');
   }
}
