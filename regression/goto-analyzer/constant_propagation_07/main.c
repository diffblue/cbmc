
int main()
{
  signed int i;
  signed int j;
  i = 0;
  if(!(i >= 2))
  {
    j = j + 1;
    i = i + 1;
    if(!(i >= 2))
    {
      j = j + 1;
      i = i + 1;
      if(!(i >= 2))
      {
        j = j + 1;
        i = i + 1;
      }
      assert(!(i < 2));
    }
  }
  return 0;
}

