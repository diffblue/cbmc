int global;

class test_class {
public:
  ~test_class() { global=1; }
};

int main() {
  test_class c, *p;

  p=&c;

  p -> ~test_class();
  
  assert(global==1);
  
  // The notation for explicit calls to destructors can be used regardless
  // of whether the type defines a destructor.  This allows you to make such
  // explicit calls without knowing if a destructor is defined for the type. 
  // An explicit call to a destructor where none is defined has no effect.

  typedef char TT;
  
  TT *q;
  q->~TT();
  
  return 0;
}
