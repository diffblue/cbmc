#define PADDING_SIZE (64 - sizeof(char) - sizeof(int))

typedef struct __attribute__((packed, aligned(64)))
{
  char uchar;
  int uint;
  char padding[PADDING_SIZE];
} a_t;

typedef struct __attribute__((packed, aligned(64)))
{
  int uint;
  char uchar;
  char padding[PADDING_SIZE];
} b_t;

typedef struct __attribute__((packed))
{
  int uint;
  char uchar;
  struct
  {
    char a;
    int b;
  } not_packed __attribute__((aligned(8)));
} c_t;

typedef struct __attribute__((packed, aligned(1)))
{
  int uint;
  char uchar;
  struct
  {
    char a;
    int b;
  } not_packed __attribute__((aligned(8)));
} d_t;

int main()
{
  _Static_assert(sizeof(a_t) == sizeof(b_t), "");
  _Static_assert(sizeof(c_t) == 8 + 2 * sizeof(int), "");
  _Static_assert(sizeof(d_t) == 8 + 2 * sizeof(int), "");
  return 0;
}
