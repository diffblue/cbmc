import org.cprover.CProver;

public class StringStrip
{
  public static void main(String[] args)
  {
    String s = "\u001C a \u001C";
    // Java 11's String.strip family removes the characters accepted by
    // Character.isWhitespace from the given end(s).
    assert s.strip().equals("a");
    assert s.stripLeading().equals("a \u001C");
    assert s.stripTrailing().equals("\u001C a");
  }

  public static void stripKeeps()
  {
    // U+001B (ESC) is not white space for Character.isWhitespace, so strip
    // keeps it, whereas trim removes all characters up to U+0020.
    String t = "\u001Ba\u001B";
    assert t.strip().equals("\u001Ba\u001B");
    assert t.trim().equals("a");
  }

  public static void unicode()
  {
    // U+2000 and U+3000 are white space, the no-break spaces U+00A0 and
    // U+2007 are not.
    String u = "\u2000\u3000a\u00A0\u2007";
    assert u.strip().equals("a\u00A0\u2007");
    assert u.trim().equals(u);
  }

  static boolean isWhite(char c)
  {
    return c == ' ' || c == '\u2000';
  }

  static boolean inAlphabet(char c)
  {
    return c == ' ' || c == '\u2000' || c == '\u001B' || c == 'a';
  }

  // Compare the strip family on a nondet string of length <= 3 over the
  // alphabet {' ', U+2000, U+001B, 'a'} with a reference implementation.
  public static void symbolic(String s, int mode)
  {
    CProver.assume(s != null && s.length() <= 3);
    for(int k = 0; k < s.length(); k++)
      CProver.assume(inAlphabet(s.charAt(k)));
    CProver.assume(mode >= 0 && mode <= 2);
    String t =
      mode == 0 ? s.strip() : mode == 1 ? s.stripLeading() : s.stripTrailing();
    int i = 0, j = s.length();
    if(mode != 2)
      while(i < j && isWhite(s.charAt(i)))
        i++;
    if(mode != 1)
      while(j > i && isWhite(s.charAt(j - 1)))
        j--;
    assert t.length() == j - i;
    for(int k = 0; k < t.length(); k++)
      assert t.charAt(k) == s.charAt(i + k);
  }

  // Each of these must fail: a witness exists.
  public static void reachEmpty(String s, int mode)
  {
    CProver.assume(s != null && s.length() == 2);
    CProver.assume(mode >= 0 && mode <= 2);
    String t =
      mode == 0 ? s.strip() : mode == 1 ? s.stripLeading() : s.stripTrailing();
    CProver.assume(t.isEmpty());
    assert false;
  }
}
