public class Test {

    static void checkStringInputValue(float f) {
      String s = Float.toString(f);
      // the 1/f is needed to distinguish -0 from 0, '==' disregards the
      // difference, while the division yields +Infinity or -Infinity.
      if (f == 0.0f && 1/f > 0) {
        assert(s.equals("0.0"));
      } else if (f == -0.0f && 1/f < 0) {
        assert(s.equals("-0.0"));
      } else if (f == 1.0f ) {
        assert(s.equals("1.0"));
      }
    }
}
