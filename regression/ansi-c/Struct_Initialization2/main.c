#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

struct A {
  int x;
  int y;
  int arr[];
};

struct _classinfo {
  char a;
  struct A s;
  int *interfaces[];
};

struct _classinfo nullclass1 = { 42, 1, 2, 0, 3, 4 };
struct _classinfo nullclass2 = { 42, { 1, 2, 0 }, { 3, 4 } };

STATIC_ASSERT(sizeof(nullclass1)==sizeof(struct _classinfo));
STATIC_ASSERT(sizeof(nullclass2)==sizeof(struct _classinfo));

int main()
{
}
