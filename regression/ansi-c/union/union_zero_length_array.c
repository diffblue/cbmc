// A zero-length array [0] is a gcc extension that has historically been
// accepted anywhere in a struct or union, independently of the more recent
// C11 rule on flexible array members ([]). This test guards that
// distinction: zero-length arrays in unions must remain accepted on all
// targets (both ISO and Windows), even after the tightening of flexible
// array members in unions.

union U
{
  int n;
  char zero_length[0];
};

int main()
{
  union U u;
  u.n = 42;
}
