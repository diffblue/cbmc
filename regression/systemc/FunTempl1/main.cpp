template<class T>
T inc(T x)
{
  return x+1;
}


int main(int argc, char** argv)
{
  int x = 1;
  unsigned char y = 2;
  x = inc<int>(x);
  x = inc<int>(x);
  y = inc<unsigned char>(y);

  __CPROVER_assert(x == y, "");
}
