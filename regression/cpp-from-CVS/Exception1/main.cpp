#include <assert.h>

class whatnot
{
public:
  whatnot(int _i):i(_i) { }
  int i;
};

int main()
{
  // example 1

  try
  {
    throw (int)0;
    assert(0);
  }
  
  catch(int i)
  {
    // yes
  }
  catch(char ch)
  {
    assert(0);
  }
  catch(whatnot)
  {
    assert(0);
  }
                  
  // example 2

  try
  {
    throw (char)0;
    assert(0);
  }
  
  catch(int i)
  {
    assert(0);
  }
  catch(char ch)
  {
  }
  catch(whatnot)
  {
    assert(0);
  }

  // example 3

  try
  {
    throw whatnot(1);
    assert(0);
  }
  
  catch(int i)
  {
    assert(0);
  }
  catch(char ch)
  {
    assert(0);
  }
  catch(whatnot w)
  {
    assert(w.i==1);
  }
}
