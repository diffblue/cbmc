interface BasicInterface
{
  int getX();
}

class Foo implements BasicInterface
{
  public int x;

  public int getX() {
    return x;
  }
}

class Bar extends Foo
{}

class GenericArray<T>
{
  public T [] t;
  public Integer [] Ia;
  public int [] ia;
}

