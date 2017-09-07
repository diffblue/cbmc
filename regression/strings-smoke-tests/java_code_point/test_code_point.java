public class test_code_point
{
   public static void main(/*String[] argv*/)
   {
      String s = "!𐤇𐤄𐤋𐤋𐤅";
      assert(s.codePointAt(1) == 67847);
      assert(s.codePointBefore(3) == 67847);
      assert(s.codePointCount(1,5) >= 2);
      assert(s.offsetByCodePoints(1,2) >= 3);
      StringBuilder sb = new StringBuilder();
      sb.appendCodePoint(0x10907);
      assert(s.charAt(1) == sb.charAt(0));
   }
}
