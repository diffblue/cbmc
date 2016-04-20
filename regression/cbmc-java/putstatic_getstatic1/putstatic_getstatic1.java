class A
{
  public static int i = 1;
};

class putstatic_getstatic1
{
  public static void main(String[] args)
  {
    assert A.i == 1;
    A.i = 999;
    assert A.i == 999;
  }
}
