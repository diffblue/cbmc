public class Test {
  // This compares the model of indexOf to an implementation
  // using loops

  public int math_min(int i, int j) {
    if (i < j)
      return i;
    else
      return j;
  }

  public int referenceLastIndexOf(String s, char ch, int fromIndex) {
    for (int i = math_min(fromIndex, s.length() - 1); i >= 0; i--) {
      if (s.charAt(i) == ch) {
        return i;
      }
    }
    return -1;
  }

  public int check(String s, char ch, int fromIndex) {
    if(s.length() <= fromIndex)
      return -1;
    int reference = referenceLastIndexOf(s, ch, fromIndex);
    int jbmc_result = s.lastIndexOf(ch, fromIndex);
    assert(reference == jbmc_result);
    return jbmc_result;
  }
}
