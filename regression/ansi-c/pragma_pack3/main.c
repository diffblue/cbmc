#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// see http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx

#pragma pack(push, 2)

struct S
{
  char c;
  int i;
};

STATIC_ASSERT(sizeof(struct S)==sizeof(int)+2);

// "The alignment of a member will be on a boundary that is either a multiple of
// n or a multiple of the size of the member, whichever is smaller."
#pragma pack(4)

struct S2
{
  short s1;
  short s2;
  int i;
};

STATIC_ASSERT(sizeof(struct S2)==sizeof(short)+sizeof(short)+sizeof(int));

struct S3
{
  short s1;
  short s2;
  short s3;
  int i;
};

STATIC_ASSERT(sizeof(struct S3)==sizeof(short)+sizeof(short)+sizeof(int)+4);

int main()
{
  return 0;
}
