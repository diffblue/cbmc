#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

//#define IO

#define K 4 //8
#define W 8 //32

#ifdef IO
#include <iostream>
#include <bitset>
#endif

typedef unsigned int uint;
typedef sc_uint<2*W+3> uint67_t;
typedef sc_uint<K*W> uint256_t;
typedef sc_uint<2*K*W> uint512_t;

uint512_t mult256_impl (uint256_t a, uint256_t b)
{
#ifdef IO
  std::cout << "a: " << a.to_uint() << std::endl;
  std::cout << "b: " << b.to_uint() << std::endl;
#endif
  //TODO: implicit conversions
  uint67_t p_product(0);  // = 0;
  uint512_t result(0); // = 0;

  uint i, k;

  /* Compute each 32-bit "digit" of p_result, propagating the carries. */
  for(k=0; k < 2*K-1; k++)
  {
    uint l_min = (k < K ? 0 : k-(K-1));
#ifdef IO
    std::cout << "k: " << k << std::endl;
    std::cout << "l_min: " << l_min << std::endl;
#endif
    for(i=l_min; i<=k && i<K; i++)
    {
      p_product += (uint67_t)a.range(W*i+W-1,W*i) * b.range(W*(k-i)+W-1,W*(k-i));
#ifdef IO
      std::cout << "i: " << i << std::endl;
      std::cout << "p_product: " << p_product.to_uint() << std::endl;
#endif
    }
    result.range(k*W+W-1,k*W) = p_product.range(W-1,0); //.to_uint();
#if 0
    std::cout << "result.range(" << (k*W+W-1) << "," << (k*W) << "): " << result.range(k*W+W-1,k*W).to_uint() << std::endl;
    std::cout << "p_product.range(" << (W-1) << ",0): " << p_product.range(W-1,0).to_uint() << std::endl;
#endif
    p_product >>= W;
#ifdef IO
    std::cout << "result: " << result.to_uint() << std::endl;
    std::cout << "p_product: " << p_product.to_uint() << std::endl;
#endif
  }

  result.range(k*W+W-1,k*W) = p_product.range(W-1,0); //.to_uint();
#ifdef IO
    std::cout << "result: " << result.to_uint() << std::endl;
#endif
  return result;
}

uint512_t bigmult (uint256_t a, uint256_t b) {
  uint512_t result = a * b;
  return result;
}

int main(int argc, char *argv[])
{
  uint256_t a(65535), b(65535);
  uint512_t spec_r, impl_r;

  spec_r = bigmult(a,b);
  impl_r = mult256_impl(a,b);

#ifdef IO
  std::cout << "spec_r: " << spec_r.to_uint() << std::endl;
  std::cout << "impl_r: " << impl_r.to_uint() << std::endl;
#endif

  assert(spec_r == impl_r);

  return 0;
}

