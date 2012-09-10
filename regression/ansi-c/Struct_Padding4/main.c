#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

struct Z1
{
  char ch;
  int i:3;
  char ch2;
  // there is end-of-struct padding because of the int
} z1;

struct Z2
{
  char ch;
  char i:3;
  char ch2;
  // there is no end-of-struct padding
} z2;

struct Z3
{
  char ch;
  int i:3; // bit-fields do not get padding!
} z3;

struct Z4
{
  int i;
  long long int x; // pads to 8
  char ch; // 7 end-of-struct padding
} z4;

struct Z5
{
  char ch;
  long long int x[]; // pads to 8, but has no size
} z5;

STATIC_ASSERT(sizeof(struct Z1)==1+1+1+1);

#ifdef __GNUC__
STATIC_ASSERT(__builtin_offsetof(struct Z1, ch2)==2);
#endif

STATIC_ASSERT(sizeof(struct Z2)==1+1+1);
STATIC_ASSERT(sizeof(struct Z3)==1+1+2);
STATIC_ASSERT(sizeof(struct Z4)==4+4+8+1+7);
STATIC_ASSERT(sizeof(struct Z5)==8);

int main()
{
}
