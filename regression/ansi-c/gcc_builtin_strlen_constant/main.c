// GCC folds __builtin_strlen of a string literal to its length at compile
// time.  The Linux kernel relies on this in module_param, which expands to
// a _Static_assert(sizeof(name) - 1 == __builtin_strlen(name), ...).
_Static_assert(__builtin_strlen("disable_ertm:bool") == 17, "len 17");
_Static_assert(
  sizeof("disable_ertm:bool") - 1 == __builtin_strlen("disable_ertm:bool"),
  "module_param pattern");
_Static_assert(__builtin_strlen("") == 0, "empty");
_Static_assert(__builtin_strlen("a") == 1, "one");

// strlen counts up to the first NUL, not the whole stored literal
_Static_assert(__builtin_strlen("a\0b") == 1, "embedded NUL");

// also usable as an array size (constant context)
char buf[__builtin_strlen("hello")];
_Static_assert(sizeof(buf) == 5, "array size from strlen");

int main(void)
{
  return sizeof(buf);
}
