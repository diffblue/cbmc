int foo(int x)
{
  if (x==3)
  {
    return 0;
  }
  else
  {
    return 3;
  }
}

void recurse(int low)
{
  if(low >= 2)
  {
    recurse(low-1);
    recurse(low-2);
  } 
  else
  {
    foo(2);
    foo(3);
    return;
  }
}

int main()
{
  recurse(5);
  return 0;
}
