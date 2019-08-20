public class StringBuilderConstructors01
{
  public static void noArgPass() {
    StringBuilder buffer1 = new StringBuilder();
    assert buffer1.length() == 0;
  }

  public static void noArgFail() {
    StringBuilder buffer1 = new StringBuilder();
    assert buffer1.length() != 0;
  }

  public static void capacityPass() {
    StringBuilder buffer2 = new StringBuilder(10);
    assert buffer2.length() == 0;
  }

  public static void capacityFail() {

    StringBuilder buffer2 = new StringBuilder(10);
    assert buffer2.length() != 0;
  }

  public static void stringPass() {
    StringBuilder buffer3 = new StringBuilder("diffblue");
    assert buffer3.length() == 8;
  }

  public static void stringFail() {
    StringBuilder buffer3 = new StringBuilder("diffblue");
    assert buffer3.length() != 8;
  }
}
