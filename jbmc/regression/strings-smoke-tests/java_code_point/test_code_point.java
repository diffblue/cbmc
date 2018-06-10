public class test_code_point
{
   public static void main()
   {
      String s = "!𐤇𐤄𐤋𐤋𐤅";
      assert(org.cprover.CProverString.codePointAt(s, 1) == 67847);
      assert(org.cprover.CProverString.codePointBefore(s, 3) == 67847);
      assert(org.cprover.CProverString.codePointCount(s,1,5) >= 2);
      assert(org.cprover.CProverString.offsetByCodePoints(s,1,2) >= 3);
      StringBuilder sb = new StringBuilder();
      sb.appendCodePoint(0x10907);
      assert(org.cprover.CProverString.charAt(s, 1) == org.cprover.CProverString.charAt(sb.toString(), 0));
   }
}
