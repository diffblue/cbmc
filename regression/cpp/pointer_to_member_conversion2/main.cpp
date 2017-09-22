class B
{
};

class D: public B
{
public:
  int x;
};

class E
{
public:
  int y;
};


int main(int argc, char** argv)
{
  int B::* xptr=static_cast<int B::*>(&D::x);
#if 0
  B b;
  b.*xptr; // undefined
#endif

  E e;
  e.*xptr; // compiler error

  return 0;
}
