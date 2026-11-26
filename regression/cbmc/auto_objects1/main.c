int main()
{
  int *auto_object_source1;
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
  if(auto_object_source1 != 0)
    int dummy = *auto_object_source1; // triggers creating an auto object
#pragma CPROVER check pop
  if(auto_object_source1 != 0 && *auto_object_source1 == 42) // uses auto object
  {
    __CPROVER_assert(*auto_object_source1 == 42, "42");
  }
}
