public class NondetEnumOpaqueReturn {

  public static void canChooseSomeConstant() {
    Opaque o = new Opaque();
    Color c = o.getC();
    if (c == null)
      return;
    assert c != null;
    boolean isRed = c.name().startsWith("RED") && c.name().length() == 3
      && c.ordinal() == 0;
    boolean isGreen = c.name().startsWith("GREEN") && c.name().length() == 5
      && c.ordinal() == 1;
    boolean isBlue = c.name().startsWith("BLUE") && c.name().length() == 4
      && c.ordinal() == 2;
    assert (isRed || isGreen || isBlue);
  }

  public static void canChooseRed() {
    Opaque o = new Opaque();
    Color c = o.getC();
    if (c == null)
      return;
    boolean isGreen = c.name().startsWith("GREEN") && c.name().length() == 5
      && c.ordinal() == 1;
    boolean isBlue = c.name().startsWith("BLUE") && c.name().length() == 4
      && c.ordinal() == 2;
    assert (isGreen || isBlue);
  }

  public static void canChooseGreen() {
    Opaque o = new Opaque();
    Color c = o.getC();
    if (c == null)
      return;
    boolean isRed = c.name().startsWith("RED") && c.name().length() == 3
      && c.ordinal() == 0;
    boolean isBlue = c.name().startsWith("BLUE") && c.name().length() == 4
      && c.ordinal() == 2;
    assert (isRed || isBlue);
  }

  public static void canChooseBlue() {
    Opaque o = new Opaque();
    Color c = o.getC();
    if (c == null)
      return;
    boolean isRed = c.name().startsWith("RED") && c.name().length() == 3
      && c.ordinal() == 0;
    boolean isGreen = c.name().startsWith("GREEN") && c.name().length() == 5
      && c.ordinal() == 1;
    assert (isRed || isGreen);
  }

}
