class Test {
  public void testBooleanSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(true);
    assert sb.toString().equals("abctrue");
  }

  public void testCharSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    sb.append('a');
    assert sb.toString().equals("abca");
  }

  public void testIntSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(3);
    assert sb.toString().equals("abc3");
  }

  public void testLongSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(3L);
    assert sb.toString().equals("abc3");
  }

  public void testCharSequenceSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    CharSequence cs = "xyz";
    sb.append(cs);
    assert sb.toString().equals("abcxyz");
  }

  public void testStringBufferSuccess() {
    StringBuffer sb = new StringBuffer("abc");
    StringBuffer buf = new StringBuffer("xyz");
    sb.append(buf);
    assert sb.toString().equals("abcxyz");
  }

  public void testBooleanNoPropagation(boolean b) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(b);
    assert sb.toString().equals("abctrue");
  }

  public void testCharNoPropagation(char c) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(c);
    assert sb.toString().equals("abca");
  }

  public void testIntNoPropagation(int i) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(i);
    assert sb.toString().equals("abc3");
  }

  public void testLongNoPropagation(long l) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(l);
    assert sb.toString().equals("abc3");
  }

  public void testCharSequenceNoPropagation(CharSequence cs) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(cs);
    assert sb.toString().equals("abcxyz");
  }

  public void testStringBufferNoPropagation(StringBuffer buf) {
    StringBuffer sb = new StringBuffer("abc");
    sb.append(buf);
    assert sb.toString().equals("abcxyz");
  }
}
