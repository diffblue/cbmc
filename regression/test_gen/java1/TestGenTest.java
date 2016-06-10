class A
{
  public int a_field_0;
  public int a_field_1;

  public A(int a_field_0)
  {
    this.a_field_0=a_field_0;
  }
}

class B extends A
{
  public int b_field_0;

  public B()
  {
    super(999);
  }
}

class C
{
  public int c_field_0;
  public B c_field_1;

  public C(int c_field_0, B c_field_1)
  {
    this.c_field_0=c_field_0;
    this.c_field_1=c_field_1;
  }
}

public class TestGenTest
{
  public static void f(B param0, C param1, int param2)
  {
    B b = null;
    int x=b.b_field_0;
    assert x != 0;
    /*int a_field_0=param0.a_field_0;
    int a_field_1=param0.a_field_1;
    int b_field_0=param0.b_field_0;
    int c_field_0=param1.c_field_0;
    int c_field_1_a_field_0=param1.c_field_1.a_field_0;
    int c_field_1_a_field_1=param1.c_field_1.a_field_1;
    int c_field_1_b_field_0=param1.c_field_1.b_field_0;

    assert a_field_0           != 499 ||
           a_field_1           != 498 ||
           b_field_0           != 497 ||
           c_field_0           != 496 ||
           c_field_1_a_field_0 != 495 ||
           c_field_1_a_field_1 != 494 ||
           c_field_1_b_field_0 != 493 ||
           param2              != 492;*/
  }
}
