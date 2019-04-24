#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// see http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx

// Debian packages owfs, gtkwave
#pragma pack(push)
#pragma pack(1)
// possibly some structs
#pragma pack(pop)

struct S
{
  char c;
  int i;
};

STATIC_ASSERT(sizeof(struct S)==2*sizeof(int));

int main()
{
  return 0;
}
