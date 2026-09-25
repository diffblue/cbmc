// Template constructor with default template arguments that reference
// class template parameters.
template <typename T1, typename T2>
struct mypair
{
  T1 first;
  T2 second;

  template <typename U1 = T1, typename U2 = T2>
  mypair() : first(), second()
  {
  }
};

int main()
{
  mypair<int, int> p;
  __CPROVER_assert(p.first == 0, "default init first");
  __CPROVER_assert(p.second == 0, "default init second");
}
