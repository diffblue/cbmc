// $Id: bigint-func.cc,v 1.1.1.1 2002-06-13 22:00:30 kroening Exp $
// Author: Dirk Zoller
// References:
//
// [1] Hüttenhofer/Lesch/Peyerimhoff, Mathematik in Anwendung mit C++
//     Heidelberg, Wiesbaden 1994

#include "bigint.hh"


BigInt
pow (BigInt const &x, unsigned y)
{
  BigInt a = x;
  BigInt r = 1;
  for (;;)
    {
      if (y & 1)
	r *= a;
      y >>= 1;
      if (y == 0)
	return r;
      a *= a;
    }
}


// Modular exponentiation, see [1] p. 74.

BigInt
pow (BigInt const &x, BigInt const &y, BigInt const &m)
{
  BigInt a = x;
  BigInt b = y;
  BigInt r = 1;
  for (;;)
    {
      a %= m;
      if (b.is_odd())
	{
	  r *= a;
	  r %= m;
	}
      b /= 2;
      if (b.is_zero())
	return r;
      a *= a;
    }
}


// Integer square root. see [1] p.23, slightly changed for better performance.

BigInt
sqrt (BigInt const &n)
{
  BigInt x0 = n;
  BigInt x1 = n;
  x1 += 1;
  x1 /= 2;
  while (x1 < x0)
    {
      x0 = x1;
      x1 += n / x0;
      x1 /= 2;
    }
  return x0;
}


BigInt
gcd (const BigInt &X, const BigInt &Y)
{
  BigInt x (X);
  BigInt y (Y);
  for (;;)
    {
      if (y.is_zero())
	return x;
      x %= y;
      if (x.is_zero())
	return y;
      y %= x;
    }
}


// Modular inverse, see [1] p.35
// Returns i in range 1..m-1 such that i*a = 1 mod m.
// a must be in range 1..m-1.

BigInt
modinv (const BigInt &a, const BigInt &m)
{
  BigInt j (1), i (0);
  BigInt b (m), c (a);
  BigInt x, y;
  while (!c.is_zero())
    {
      BigInt::div (b, c, x, y);
      b = c;
      c = y;
      y = j;

      // j = i - j * x; trading clarity for efficiency.
      j *= x;
      j -= i;
      j.negate();

      i = y;
    }
  if (i.is_negative())
    i += m;
  return i;
}
