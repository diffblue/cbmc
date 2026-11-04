struct S
{
  int x, y;
};

int main()
{
  // Struct values are emitted using SMT datatypes (use_datatypes is enabled
  // for this encoder so that whole-struct values can be expressed). The SMT2
  // output therefore declares a datatype for struct S.
  struct S s;
  s.x = 1;
  __CPROVER_assert(s.x == 1, "property 1");
  return 0;
}
