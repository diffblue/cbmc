struct A { virtual int f(){ return 1; } };
struct B { virtual int f(){ return 2;} };
struct C: A,B { virtual int f(){ return 3;} };


int main(int argc, char* argv[])
{
  C c;
  C c2(c);
  assert(((A&)c2).f() == ((B&)c2).f());
  return 0;
}

