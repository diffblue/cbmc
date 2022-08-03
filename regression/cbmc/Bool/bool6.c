int main()
{
  _Bool u = 1;
  _Bool *p = &u;

  // combination of _Bool, dereference, and pre-increment side-effect
  if(++(*p) != 1)
    __CPROVER_assert(0, "");

  // combination of _Bool, dereference, and compound assignment side-effect
  if(((*p) += 1) != 1)
    __CPROVER_assert(0, "");

  // combination of _Bool, dereference, and assignment side-effect
  if(((*p) = 1) != 1)
    __CPROVER_assert(0, "");

  __CPROVER_assert(*p == 1, "");
}
