#include <assert.h>

void dll_create_generic(void (*insert_fnc)())
{
  int x;
  insert_fnc(&x);
}

void dll_insert_master(int *a) 
{
  assert(0);
}

int main()
{
  dll_create_generic(dll_insert_master);
  return 0;
}

