#include <cassert>

int i;

struct B
{
  B() { i++; }
  B(const B& b) { i+=10; }
};


B f(B b)
{
  assert(i==11);
  return b;  
}


int main()
{
  B b;
  b = f(b);
  assert(i==21);
}
