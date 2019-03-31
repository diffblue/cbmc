template <int W>
class sc_uint {
  public:
    sc_uint(unsigned long v)
    {
      m_val = v;
    }

  sc_uint<W> &operator=(const sc_uint &other)
  {
    m_val = other.m_val;
    return *this;
  }

  bool operator==(const sc_uint &other)
  {
    return m_val == other.m_val;
  }

#if 0
  sc_uint<W> operator+(const sc_uint &other)
  {
    return sc_uint(m_val + other.m_val);
  }
#endif

  sc_uint<W> operator += (const sc_uint &other)
  {
    m_val += other.m_val;
    return *this;
  }

  sc_uint<W> operator += (unsigned long v)
  {
    m_val += v;
    return *this;
  }

protected:
  unsigned long m_val;
};


int main(int argc, char** argv)
{
  sc_uint<10> x(1);
  sc_uint<10> y(2);

//  sc_uint<10> z = x+y;
  sc_uint<10> z(0);
  z += x;
  z += y;

  sc_uint<10> w(3);
  __CPROVER_assert(z == w, "");

  return 0;
}
