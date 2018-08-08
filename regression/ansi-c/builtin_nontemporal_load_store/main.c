int main()
{
  #ifdef __clang__
  int var, value;
  __builtin_nontemporal_store(1, &var);
  value = __builtin_nontemporal_load(&var);
  #endif
}
