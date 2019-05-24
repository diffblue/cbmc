public enum Color {
  RED(false),
  BLUE(false),
  GREEN(false),
  WHITE(true),
  GREY(true),
  BLACK(true);

  private boolean grayscale;

  Color(boolean grayscale) {
    this.grayscale = grayscale;
  }

  public boolean isGrayscale() {
    return grayscale;
  }

  public static Color enumField = Color.WHITE;
  public static void testEnumInOwnTypePass() {
    assert enumField == Color.WHITE && enumField.name().equals("WHITE") &&
        enumField.ordinal() == 3 && enumField.isGrayscale();
  }
  public static void testEnumInOwnTypeFail() {
    assert enumField != Color.WHITE || !enumField.name().equals("WHITE") ||
        enumField.ordinal() != 3 || !enumField.isGrayscale();
  }

}
