import org.cprover.CProver;
public class SymbolicTrim {
  static boolean ok(char c) {
    return c == ' ' || c == '\n' || c == '\u0001' || c == 'a' || c == '!';
  }
  // s is a nondet string of length <= 4 over {' ', '\n', '\u0001', 'a', '!'};
  // the result of trim is compared with a reference computed by loops.
  public static void check(String s) {
    CProver.assume(s != null && s.length() <= 4);
    for(int k = 0; k < s.length(); k++)
      CProver.assume(ok(s.charAt(k)));
    String t = s.trim();
    int i = 0, j = s.length();
    while(i < j && s.charAt(i) <= ' ') i++;
    while(j > i && s.charAt(j - 1) <= ' ') j--;
    assert t.length() == j - i;
    for(int k = 0; k < t.length(); k++)
      assert t.charAt(k) == s.charAt(i + k);
  }
  // Completeness probes: each of these must FAIL (a witness exists).
  public static void reachAllSpace(String s) {
    CProver.assume(s != null && s.length() == 3);
    CProver.assume(s.trim().isEmpty());
    assert false;
  }
  public static void reachLeadingOnly(String s) {
    CProver.assume(s != null && s.length() == 3);
    String t = s.trim();
    CProver.assume(t.length() == 2 && s.charAt(0) == '\u0001');
    assert false;
  }
  public static void reachTrailingOnly(String s) {
    CProver.assume(s != null && s.length() == 3);
    String t = s.trim();
    CProver.assume(t.length() == 2 && s.charAt(2) == ' ');
    assert false;
  }
  public static void reachEmpty(String s) {
    CProver.assume(s != null && s.length() == 0);
    CProver.assume(s.trim().length() == 0);
    assert false;
  }
}
