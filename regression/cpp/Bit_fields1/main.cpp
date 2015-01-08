typedef int INT;

typedef enum { E1=1 } some_enum_type;

struct some_struct {
  unsigned int a:3;
  unsigned int b:1;
  signed int c:2;

  // an anonymous bitfield
  signed int :2;
  
  // with typedef
  INT x:1;
  
  // made of sizeof
  unsigned int abc: sizeof(int);

  // enums are integers!
  some_enum_type enum_field1 : 5;
  
  // and good as field sizes
  some_enum_type enum_field2 : E1;
} X;

template<typename T> class trait { public: enum { t=0 }; };
template<> class trait<unsigned> { public: enum { t=1 }; };
template<> class trait<signed> { public: enum { t=2 }; };
template<> class trait<some_enum_type> { public: enum { t=3 }; };

static_assert(trait<decltype(X.a)>::t==1, "X.a");
static_assert(trait<decltype(X.c)>::t==2, "X.c");
static_assert(trait<decltype(X.x)>::t==2, "X.x");
static_assert(trait<decltype(X.enum_field1)>::t==3, "X.enum_field1");

int main()
{
}
