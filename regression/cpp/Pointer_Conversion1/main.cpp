int f()
{
}

int main()
{
  void *p;
  // this works in C, but not C++
  p=f;
}
