extern "C" void __CPROVER_assert(bool, const char *);

// GCC's `enum __attribute__((__packed__))` extension: with no
// enumeration-base written, the underlying type is the smallest
// sufficient integer type (N5008 [dcl.enum]/8 leaves it
// implementation-defined; g++ and clang++ shrink).  User-reported:
// firmware ABIs pack enums to get 1-byte instruction fields, and the
// C++ front end ignored the attribute while the C front end honoured
// it.
typedef enum
{
  A = 0,
  B = 1
} __attribute__((__packed__)) E1;
typedef enum
{
  N = -1,
  P = 100
} __attribute__((__packed__)) E2;
typedef enum
{
  W = 100000
} __attribute__((__packed__)) E3;
typedef struct
{
  E1 e;
  unsigned char b;
} __attribute__((__packed__)) S;

static_assert(sizeof(E1) == 1, "packed enum is 1 byte");
static_assert(sizeof(E2) == 1, "negative range fits signed char");
static_assert(sizeof(E3) == 4, "wide range still needs 4 bytes");
static_assert(sizeof(S) == 2, "packed struct with packed enum member");

// Attribute between enum-key and name ([dcl.enum]/1 grammar position).
enum __attribute__((__packed__)) E5
{
  Y = 1
};
static_assert(sizeof(E5) == 1, "attribute before name also shrinks");

// N5008 [dcl.enum]/5: scoped enums have a FIXED underlying type (int
// when unspecified); the packed attribute does not shrink them.
enum class __attribute__((__packed__)) E4
{
  X = 1
};
static_assert(sizeof(E4) == sizeof(int), "scoped enum stays int");

int main()
{
  E2 x = N;
  __CPROVER_assert(x == -1, "negative enumerator value preserved");
  __CPROVER_assert(static_cast<int>(P) == 100, "value preserved");
  return 0;
}
