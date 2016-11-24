class C
{
  public:
    C(int& v):v(v){};
    int v;
};

struct D
{
  int r;
};

int main(int argc, char* argv[])
{
  int i=10;
  int& ref = i;
  C* pc = new C((char&)ref);
  assert(pc->v == 10);
  D d;
  d.r = 10;
  D& ref_d = d;
  D* pd = new D(ref_d);
  assert(pd->r == 10);
}

