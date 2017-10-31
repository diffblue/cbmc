int const C=10;

int main()
{
  __CPROVER_assert(C == 10, "");

  // this is *not* allowed
  ((int &)C)=20;
}
