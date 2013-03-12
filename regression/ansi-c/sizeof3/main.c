#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

struct empty_struct { };
union empty_union { };

struct combination {
  int id;
  struct { } s;
  union { } u;
};

STATIC_ASSERT(sizeof(struct empty_struct)==0);
STATIC_ASSERT(sizeof(union empty_union)==0);
STATIC_ASSERT(sizeof(struct combination)==sizeof(int));

int main()
{
}
