class string_literal1
{
  public static void main(String[] args)
  {
    String s1="abc";
    assert s1.equals("abc");

    int size="ABCxyz".length();
    assert size==6;
  }
}

