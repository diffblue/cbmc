// An alignment attribute following a member's declarator must be a positive
// power of two, also when it is given as a constant expression rather than a
// literal.
struct S
{
  int a;
  int grp __attribute__((aligned(5 + 0)));
};

struct S s;

int main(void)
{
  return 0;
}
