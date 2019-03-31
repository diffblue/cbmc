template <int W>
class sc_uint {
  public:
    sc_uint(unsigned long v)
    {
      val = v;
    }

  sc_uint<W> &operator=(const sc_uint &other)
  {
    val = other.val;
    return *this;
  }

  bool operator==(const sc_uint &other)
  {
    return val == other.val;
  }

#if 0
  sc_uint<W> operator+(const sc_uint &other)
  {
    return sc_uint(val + other.val);
  }
#endif

  sc_uint<W> operator += (const sc_uint &other)
  {
    val += other.val;
    return *this;
  }

#if 0
  sc_uint<W> operator += (unsigned long v)
  {
    val += v;
    return *this;
  }
#endif

protected:
  __CPROVER::unsignedbv<W> val;

};


int main(int argc, char** argv)
{
  sc_uint<10> x(1);
  sc_uint<10> y(2);

  sc_uint<10> z(0);
  z += x;
  z += y;

  sc_uint<10> w(3);
  __CPROVER_assert(z == w, "");

  return 0;
}
