// Template constructor in non-template class, called through template param
struct S
{
  S()
  {
  }
  template <typename T>
  S(T begin, T end)
  {
  }
};

template <typename Type>
void create(int *p)
{
  Type t(p, p);
}

int main()
{
  int a[2];
  create<S>(a);
}
