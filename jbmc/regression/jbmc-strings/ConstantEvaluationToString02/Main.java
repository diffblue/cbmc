public class Main {
  public void testPropagation() {
    assert Integer.toString(7).equals("7");
    assert Integer.toString(0xff, 16).equals("ff");
    assert Long.toString(7L).equals("7");
    assert Long.toString(0xffL, 16).equals("ff");
    assert Byte.toString((byte)7).equals("7");
    assert Short.toString((short)7).equals("7");
  }
}
