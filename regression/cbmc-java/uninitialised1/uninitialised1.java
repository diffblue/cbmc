class uninitialised1
{
  public static void main(String[] args)
  {
    int i[] = new int[1];
    assert i[0] == 0;
  }
}
