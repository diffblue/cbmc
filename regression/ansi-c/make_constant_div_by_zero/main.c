// 1/0 is not folded by the simplifier, so it is not a compile-time constant
// expression; using it as a file-scope array size must be rejected.  This
// guards that the extra operators accepted for Clang's __builtin_constant_p
// folding (in clang_is_constant_foldedt) were NOT added to the shared
// is_compile_time_constantt base predicate that make_constant consults --
// i.e. that make_constant's behaviour is unchanged by that work.
int a[1 / 0];

int main()
{
  return 0;
}
