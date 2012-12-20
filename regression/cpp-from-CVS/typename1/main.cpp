class X
{
public:
  typedef int T;
};

template<class Z> class Y
{
public:
  typename X::T g;
  
  void f()
  {
    typename X::T l;
  
  }
};

int main()
{
  Y<int> o;
  
  o.g=1;
}
