extern "C" void __CPROVER_assert(bool, const char *);
const char a[3] = "ab";
// GCC's typeof extension (gcc.gnu.org/onlinedocs/gcc/Typeof.html, also
// accepted by Clang): __typeof__(a[0]) is the type of the expression a[0],
// const char
int main()
{
  __typeof__(a[0]) c = 'x';
  __CPROVER_assert(c == 'x', "typeof subscript");
  __CPROVER_assert(c != 'x', "WRONG (must FAIL)");
}
