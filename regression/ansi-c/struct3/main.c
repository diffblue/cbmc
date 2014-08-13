#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

struct A
{
  int a;
  int b;
};

int main()
{
  struct A
  {
    int a;
  };
  STATIC_ASSERT(sizeof(struct A)==sizeof(int));

  return 0;
}
