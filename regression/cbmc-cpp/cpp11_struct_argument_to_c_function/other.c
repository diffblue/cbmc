struct pair
{
  int first;
  struct
  {
    int second;
  } inner;
};

int sum(struct pair p)
{
  return p.first + p.inner.second;
}
