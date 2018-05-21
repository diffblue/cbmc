class A1
{
  int some_member;
  
  A1() { some_member=1; }
};

class A2 extends A1
{
  int some_other_member;

  A2() { some_other_member=2; }
};

class A3 extends A2
{
  int yet_another_member;

  A3() { yet_another_member=3; }
};

class Inheritance1
{
  public static void main(String[] args)
  {
    A3 a3=new A3();
    assert a3.some_member==1;
    assert a3.some_other_member==2;
    assert a3.yet_another_member==3;
  }
}

