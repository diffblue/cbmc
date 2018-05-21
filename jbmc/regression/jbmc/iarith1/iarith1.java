class iarith1
{
  public static void main(String[] args)
  {
    int i = 99;
    ++i;
    int tmp = i + 2;
    i = tmp;
    tmp = i - 3;
    i = tmp;
    i += 3;
    i -= 3;
    tmp = i * 2;
    i = tmp;
    tmp = i / 3;
    i = tmp;
    i %= 34;
    i = -i;
    assert i == -32;
    long l = 99;
    ++l;
    l += 2L;
    l -= 3L;
    l *= 2L;
    l /= 3L;
    l %= 34L;
    l = -l;
    assert l == -32L;
  }
}

