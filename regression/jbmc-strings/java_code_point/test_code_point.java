public class test_code_point
{
   public static void main(/*String[] argv*/)
   {
      String s = "!𐤇𐤄𐤋𐤋𐤅";
      StringBuilder sb = new StringBuilder();
      sb.appendCodePoint(0x10907);
      assert(s.codePointAt(1) != 67847 ||
             s.codePointBefore(3) != 67847 ||
             s.codePointCount(1,5) < 2 ||
             s.offsetByCodePoints(1,2) < 3  ||
             s.charAt(1) != sb.charAt(0));
   }
}
