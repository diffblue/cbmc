#include <assert.h>

int my_global;

void dll_create_generic(void (*insert_fnc)())
{
  insert_fnc(&my_global);
}

void dll_insert_master(int *a) 
{
  *a=123;
}

int main()
{
  dll_create_generic(dll_insert_master);
  assert(my_global==123);
  
  return 0;
}
