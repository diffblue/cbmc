public class TestDeleteCharAt
{
   public static void testStringBuilderSuccess(boolean b)
   {
      String s = b ? "abc" : "xyz";
      StringBuilder sb = new StringBuilder(s);
      org.cprover.CProverString.deleteCharAt(sb, 1);
      String result = sb.toString();
      assert !b || result.equals("ac");
      assert b || result.equals("xz");
   }

   public static void testStringBuilderFailure(boolean b)
   {
      String s = b ? "abc" : "xyz";
      StringBuilder sb = new StringBuilder(s);
      org.cprover.CProverString.deleteCharAt(sb, 1);
      String result = sb.toString();
      assert !b || result.equals("ab");
      assert b || result.equals("yz");
   }

   public static void testStringBufferSuccess(boolean b)
   {
      String s = b ? "abc" : "xyz";
      StringBuffer sb = new StringBuffer(s);
      org.cprover.CProverString.deleteCharAt(sb, 1);
      String result = sb.toString();
      assert !b || result.equals("ac");
      assert b || result.equals("xz");
   }

   public static void testStringBufferFailure(boolean b)
   {
      String s = b ? "abc" : "xyz";
      StringBuffer sb = new StringBuffer(s);
      org.cprover.CProverString.deleteCharAt(sb, 1);
      String result = sb.toString();
      assert !b || result.equals("ab");
      assert b || result.equals("yz");
   }
}
