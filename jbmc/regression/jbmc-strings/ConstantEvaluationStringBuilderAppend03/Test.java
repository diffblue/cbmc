class Test {
  public void testBooleanSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(true);
    assert sb.toString().equals("abctrue");
  }

  public void testCharSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    sb.append('a');
    assert sb.toString().equals("abca");
  }

  public void testIntSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(3);
    assert sb.toString().equals("abc3");
  }

  public void testLongSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(3L);
    assert sb.toString().equals("abc3");
  }

  public void testCharSequenceSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    CharSequence cs = "xyz";
    sb.append(cs);
    assert sb.toString().equals("abcxyz");
  }

  public void testStringBufferSuccess() {
    StringBuilder sb = new StringBuilder("abc");
    StringBuffer buf = new StringBuffer("xyz");
    sb.append(buf);
    assert sb.toString().equals("abcxyz");
  }

  public void testBooleanNoPropagation(boolean b) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(b);
    assert sb.toString().equals("abctrue");
  }

  public void testCharNoPropagation(char c) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(c);
    assert sb.toString().equals("abca");
  }

  public void testIntNoPropagation(int i) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(i);
    assert sb.toString().equals("abc3");
  }

  public void testLongNoPropagation(long l) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(l);
    assert sb.toString().equals("abc3");
  }

  public void testCharSequenceNoPropagation(CharSequence cs) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(cs);
    assert sb.toString().equals("abcxyz");
  }

  public void testStringBufferNoPropagation(StringBuffer buf) {
    StringBuilder sb = new StringBuilder("abc");
    sb.append(buf);
    assert sb.toString().equals("abcxyz");
  }
}
