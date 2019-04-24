int identifier_\u0201_;
int \u0201_abc;

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

char my_string[]="\u0201";
STATIC_ASSERT(sizeof(my_string)==3);

// also as character literal
STATIC_ASSERT(L'\u0201'==0x0201);

int main()
{
  identifier_ȁ_=10;
  ȁ_abc=10;
}
