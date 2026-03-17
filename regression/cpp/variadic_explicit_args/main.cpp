template <typename T, typename... Args>
T *make(Args &&...args)
{
  return new T();
}

struct S
{
};

int main()
{
  S *p = make<S>();
  delete p;
  return 0;
}
