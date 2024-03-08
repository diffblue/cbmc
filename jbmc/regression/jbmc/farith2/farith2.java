class farith2
{
  public static void main(String[] args)
  {
    // examples from
    // https://stackoverflow.com/questions/2947044/how-do-i-use-modulus-for-float-double
    // and
    // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
    double d1 = 0.5 % 0.3;
    assert d1 == 0.2;
    double d2 = (-0.5) % 0.3;
    assert d2 == -0.2;
    double x = 7.5, y = 2.1;
    double xModY = x % y;
    assert xModY > 1.19 && xModY < 1.21;
  }
}
