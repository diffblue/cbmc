class uninitialised1
{
  public static void main(String[] args)
  {
    int i[] = new int[10];
    assert i[3] == 0;
  }
}
