public class Test {

    static void checkStringInputValue(String s) {
      if (s.equals("fo")) {
        assert(false);
      } else if (s.equals("foo")) {
        assert(false);
      } else if (s.length() == 3) {
        assert(false);
      } else if (s.equals("barr")) {
        assert(false);
      } else if (s.equals("")) {
        assert(false);
      }
      assert(false);
    }
}
