class A
{
  public static int i;
};

class putstatic_getstatic1
{
  public static void main(String[] args)
  {
    A.i = 999;
    assert 999 == A.i;
  }
}
