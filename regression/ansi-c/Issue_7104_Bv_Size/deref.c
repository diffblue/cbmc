struct Foo1
{
  __CPROVER_bitvector[1] m_array[2];
};
struct Foo8
{
  __CPROVER_bitvector[8] m_array[2];
};

int main(void)
{
  struct Foo1 f1;
  struct Foo8 f8;

  __CPROVER_assert(f1.m_array[1] == *(f1.m_array + 1), "");
  __CPROVER_assert(f8.m_array[1] == *(f8.m_array + 1), "");
  return 0;
}
