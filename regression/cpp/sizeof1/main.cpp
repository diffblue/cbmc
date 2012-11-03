
class C
{
public:
  int i;
  int j;
  
  void f()
  {
  }
};

C c;

static_assert(sizeof c==2*sizeof(int), "size of c");

static_assert(sizeof(class C)==sizeof c, "size of class C");

// this should also work
int i;

static_assert(sizeof(i)==4, "size of i");
  
// and this, too
typedef unsigned int UINT32;
static_assert(sizeof(UINT32)==4, "size of UINT32");

int main()
{
}
