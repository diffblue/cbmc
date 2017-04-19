template <unsigned int X, unsigned int Y>
struct sc_ufixed
{
  unsigned int value;

  sc_ufixed (const unsigned int x) : value(x)
  {
  }

  sc_ufixed<X*2, Y*2> multiply (const sc_ufixed<X, Y> &op) const
  {
    unsigned int result = this->value * op.value;
    return sc_ufixed<X*2, Y*2>(result);
  }

};

const sc_ufixed<1, 1> one(1U);

int main (void) {
  // const sc_ufixed<1, 1> one(1U);
  one.multiply(one);
  return 0;
}
