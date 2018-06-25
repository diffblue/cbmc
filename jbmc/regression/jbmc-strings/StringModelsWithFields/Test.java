public class Test {

  public static void testme(StringBuilder builder, StringBuffer buffer, String str) {

    // In this test the versions of String, StringBuilder and
    // StringBuffer.class supplied have fields beyond the expected situation
    // of either no fields at all (without --refine-strings) or only 'length'
    // and 'data' (with --refine-strings). We check they have been nondet-
    // initialized as expected by making sure we can reach the final
    // 'assert false'.

    if(str != null &&
       builder != null &&
       buffer != null &&
       str.a != null &&
       builder.i != null &&
       buffer.i != null &&
       str.a.x >= 5 &&
       str.a.y <= -10.0f &&
       builder.d >= 100.0 &&
       buffer.b == true) {

      assert builder instanceof StringBuilder;
      assert buffer instanceof StringBuffer;
      assert str instanceof String;

      assert str.a instanceof A;
      assert builder.i instanceof Integer;
      assert buffer.i instanceof Integer;

      assert false;
    }

  }

}
