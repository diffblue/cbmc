public class Test
{
  public static void main(String[] args)
  {
    // a letter that is not a digit in the given radix
    assert Character.digit('z', 10) == -1;
    assert Character.digit('7', 10) == 7;
    assert Character.digit('b', 16) == 11;
    assert Character.digit('B', 16) == 11;
    // a decimal digit that is not a digit in the given radix
    assert Character.digit('9', 8) == -1;
  }
}
