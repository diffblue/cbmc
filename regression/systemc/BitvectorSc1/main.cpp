template <int W>
class sc_uint {
  public:
    sc_uint(unsigned long v)
    {
      width = W;
      val = v;
    }

  void test1();
  void test2()
  {
    unsigned long a[W];
    a[W-1] = W;
  }

  unsigned long to_uint()
  {
    return val;
  }

protected:
  int width;
//  unsigned long val;
  __CPROVER::unsignedbv<W> val;

};

template<int W>
void sc_uint<W>::test1()
{
  width = W;
}


int main(int argc, char** argv)
{
  sc_uint<10> x(2);
  x.test1();
  x.test2();

  __CPROVER_assert(x.to_uint() == 1, "");
  __CPROVER_assert(x.to_uint() == 2, "");

  return 0;
}
