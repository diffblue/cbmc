#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

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

struct S3
{
  char my_bit : 1;
  int : 0; // zero width, causes padding to alignment of int
  char other;
  int whatnot;
};

STATIC_ASSERT(sizeof(struct S3)==sizeof(int)+sizeof(int)+sizeof(int));

int main()
{
  // check some operators
  struct S1 s1;
  s1.my_bit+=1;
  s1.my_bit|=1;
  s1.my_bit&=1;
  s1.my_bit^=1;
  s1.my_bit<<=1;
  s1.my_bit++;
  ++s1.my_bit;
  (unsigned)s1.my_bit;

  int *p;
  p=p+s1.my_bit;
  p=p-s1.my_bit;
  p+=s1.my_bit;
  p-=s1.my_bit;
}
