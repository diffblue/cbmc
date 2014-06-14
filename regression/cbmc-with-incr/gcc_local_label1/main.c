#include <assert.h>

// GCC has 'local labels', visible only in their respective block
void other_f()
{
  int x;

  #ifdef __GNUC__
  here:;
  x++;
  
  {
    __label__ here, there;
    
    goto here; // not jumping up, but down!

    here:; // this would usually fail
    
    assert(0);
  }
  #else
  // I don't know a Visual Studio equivalent
  assert(0);
  #endif
}

int main()
{
  other_f();
}

