#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// 6.7.9, 14: An array of character type may be initialized by a character
// string literal or UTF−8 string literal, optionally enclosed in braces.

const unsigned char A[] = { "abc" };
const unsigned char A1[] = "abc";
const unsigned char B[] = { "a" "b" "c" };
const unsigned char C[] = { 'a', 'b', 'c' };
const unsigned char C1[] = { "a", 'b', 'c' }; // 'b', 'c' to be discarded

STATIC_ASSERT(sizeof(A)==4);
STATIC_ASSERT(sizeof(A)==sizeof(A1));
STATIC_ASSERT(sizeof(B)==4);
STATIC_ASSERT(sizeof(C)==3);
STATIC_ASSERT(sizeof(C1)==2);

int main()
{

  return 0;
}
