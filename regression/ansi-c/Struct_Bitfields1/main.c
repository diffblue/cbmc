#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];

struct S1
{
  struct sub
  {
    int other : 1;
  } whatnot;

  int my_bit : 1;

  const my_bit2 : 2; // no type!
};

STATIC_ASSERT(sizeof(struct S1)==sizeof(int)*2);

struct S2
{
  char my_bit : 1;
};

STATIC_ASSERT(sizeof(struct S2)==sizeof(char));

int main()
{
}
