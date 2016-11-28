//#define STATIC_ASSERT(condition) \
//  int some_array##__LINE__[(condition) ? 1 : -1];
#define STATIC_ASSERT(condition) \
  _Static_assert((condition), "assertion");

struct A
{
  int a;
  int b;
};

int main()
{
  STATIC_ASSERT(sizeof(struct A)==sizeof(int)*2);

  struct A
  {
    int a;
  };

  STATIC_ASSERT(sizeof(struct A)==sizeof(int));

  {
    struct A
    {
      char a;
    };

    STATIC_ASSERT(sizeof(struct A)==sizeof(char));
  }

  return 0;
}
