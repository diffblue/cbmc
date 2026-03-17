struct Inner
{
  typedef int rep;
};
struct Outer
{
  typedef Inner duration;
  typedef duration::rep my_rep;
};

int main()
{
  Outer::my_rep x = 42;
  return x;
}
