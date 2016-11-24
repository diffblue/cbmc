int const C=10;

int main()
{
  assert(C==10);

  // this is *not* allowed
  ((int &)C)=20;
}
