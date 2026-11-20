struct S
{
  int x;
};

template <typename T>
S operator+(const S &a, const T &b)
{
  S r;
  r.x = a.x + b;
  return r;
}

int main()
{
  S a;
  a.x = 1;
  S b = a + 2;
  return 0;
}
