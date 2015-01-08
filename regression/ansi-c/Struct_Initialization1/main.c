#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

struct _classinfo {
  char a;
  int *interfaces[];
};

struct _classinfo nullclass1 = { 42, 0, 0 };
struct _classinfo nullclass2 = { 42, { 0, 0 } };

STATIC_ASSERT(sizeof(nullclass1)==sizeof(struct _classinfo));
STATIC_ASSERT(sizeof(nullclass2)==sizeof(struct _classinfo));

int main()
{
}
