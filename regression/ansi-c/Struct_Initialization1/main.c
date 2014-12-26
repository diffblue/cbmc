#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

struct _classinfo {
  char a;
  int *interfaces[];
};

struct _classinfo nullclass = { 42, 0, 0 };

int main()
{
}
