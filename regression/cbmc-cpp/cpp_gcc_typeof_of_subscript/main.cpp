extern "C" void __CPROVER_assert(bool, const char *);
const char a[3] = "ab";
typedef int T;
// GCC's typeof extension (gcc.gnu.org/onlinedocs/gcc/Typeof.html, also
// accepted by Clang): __typeof__(a[0]) is the type of the expression a[0],
// const char; __typeof__(T[2]) with T a type is the array type int[2]
int main()
{
  __typeof__(a[0]) c = 'x';
  __typeof__(T[2]) b = {1, 2};
  __CPROVER_assert(c == 'x', "typeof subscript");
  __CPROVER_assert(sizeof(b) == 2 * sizeof(int), "typeof array type-id");
  __CPROVER_assert(c != 'x', "WRONG (must FAIL)");
}
