#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

// see http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx

#pragma pack(push, 2)

struct S
{
  char c;
  int i;
};

STATIC_ASSERT(sizeof(struct S)==sizeof(int)+2);

int main()
{
  return 0;
}

