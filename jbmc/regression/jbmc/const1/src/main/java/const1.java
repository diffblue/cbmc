class const1
{
  public static void main(String[] args)
  {
    assert 0.0f < 1.0f;
    assert 0.0 < 1.0;
    assert 1.0f < 2.0f;
    assert -1 < 0;
    assert 1 < 2;
    assert 3 < 4;
    assert 4 < 5;
    assert 0L < 1L;
    assert 98 < 99;
    assert 98.0 < 99.0;
    assert 98.0f < 99.0f;
    assert 98L < 99L;
    
    int i = 0;
    assert i == 0;
    ++i;
    assert i == 1;
    ++i;
    assert i == 2;
    ++i;
    assert i == 3;
  }
}

