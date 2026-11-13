public class test_code_point
{
   public static void main()
   {
      String s = "!𐤇𐤄𐤋𐤋𐤅";
      assert(org.cprover.CProverString.codePointAt(s, 1) == 67847);
      assert(org.cprover.CProverString.codePointBefore(s, 3) == 67847);
      assert(org.cprover.CProverString.codePointCount(s,1,5) >= 2);
      assert(org.cprover.CProverString.offsetByCodePoints(s,1,2) >= 3);
      // StringBuilder.appendCodePoint with a supplementary-plane code point:
      // the result must be the high+low surrogate pair encoding 0x10907.
      StringBuilder sb = new StringBuilder();
      sb.appendCodePoint(0x10907);
      assert(org.cprover.CProverString.charAt(s, 1) == org.cprover.CProverString.charAt(sb.toString(), 0));
      assert(org.cprover.CProverString.charAt(s, 2) == org.cprover.CProverString.charAt(sb.toString(), 1));
      assert(sb.length() == 2);
      // StringBuilder.appendCodePoint with a Basic-Multilingual-Plane code
      // point: the result must be a single UTF-16 code unit equal to the
      // input value.
      StringBuilder sb_bmp = new StringBuilder();
      sb_bmp.appendCodePoint(0x4E2D);
      assert(sb_bmp.length() == 1);
      assert(org.cprover.CProverString.charAt(sb_bmp.toString(), 0) == 0x4E2D);
      // StringBuffer.appendCodePoint should behave the same way; exercise
      // both the supplementary-plane and the BMP branches.
      StringBuffer buf = new StringBuffer();
      buf.appendCodePoint(0x10907);
      buf.appendCodePoint(0x4E2D);
      assert(buf.length() == 3);
      assert(org.cprover.CProverString.charAt(buf.toString(), 0) == org.cprover.CProverString.charAt(s, 1));
      assert(org.cprover.CProverString.charAt(buf.toString(), 1) == org.cprover.CProverString.charAt(s, 2));
      assert(org.cprover.CProverString.charAt(buf.toString(), 2) == 0x4E2D);
   }
}
