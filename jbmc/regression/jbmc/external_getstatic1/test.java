class A
{
  public static A external_global;
  public int i;
};

public class test
{
  public static void main()
  {
    if(A.external_global == null)
      return;
    A local = A.external_global;
    assert(local instanceof A);
  }
}
