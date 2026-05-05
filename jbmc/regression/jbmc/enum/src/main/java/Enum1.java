public enum Enum1
{
  VAL1, VAL2, VAL3, VAL4, VAL5;
  static
  {
    for(Enum1 e : Enum1.values())
    {
      System.out.println(e);
    }
  }
  public static void main(String[] args)
  {
    Enum1 e=VAL5;
    assert(e==VAL5);
  }
}
