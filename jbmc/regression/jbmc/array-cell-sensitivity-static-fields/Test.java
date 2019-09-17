class Util {
  public static char[] chars(int count) {
    char result[] = new char[count];
    for (int i = 0; i < count; ++i) {
      result[i] = (char)((int)'a' + i);
    }
    return result;
  }
}

public class Test {
  // static field which is initialized to a non-empty value
  public static char[] staticCharArray = Util.chars(26);
  // reference to the same array
  public static char[] staticCharArrayRef = staticCharArray;

  public static char[] charArray() {
    staticCharArray[0] = staticCharArray[3];
    staticCharArray[1] = 'e';
    assert staticCharArray[0] == 'd';
    assert staticCharArray[0] == 'A';
    return staticCharArray;
  }

  public static char[] charArrayRef() {
    staticCharArrayRef[0] = staticCharArray[3];
    staticCharArray[1] = 'e';
    if (staticCharArray[0] == 'A') {
      assert false;
    } else if (staticCharArray[0] == 'd') {
      assert false;
    }

    return staticCharArray;
  }
}
