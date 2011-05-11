// $Id: bigint.cc,v 1.5 2010-12-28 16:14:18 kroening Exp $

// My own BigInt class, implementation.

// The copyright at this source is owned Dirk Zoller.
// You may however use and modify this without restriction.

#include "bigint.hh"
#include "allocainc.h"

#include <ctype.h>
#include <limits.h>
#include <string.h>

// How to report errors.
#include <stdio.h>
#define error(x) fprintf (stderr, "%s\n", x)


// Shortcut access to BigInt scoped things.
typedef BigInt::llong_t  llong_t;
typedef BigInt::ullong_t ullong_t;
typedef BigInt::onedig_t onedig_t;
typedef BigInt::twodig_t twodig_t;

static const unsigned small	 = BigInt::small;
static const int     single_bits = sizeof (onedig_t) * CHAR_BIT;
static const twodig_t base       = twodig_t (1) << single_bits;
static const twodig_t single_max = base - 1;


inline unsigned
adjust_size (unsigned size)
{
  // Always allocate at least something greater than an ullong_t.
  if (size <= small)
    size = small + 1;

  // Assuming the heap works with a specific granularity G and needs
  // space B for a few bookkeeping pointers: Prefer allocation sizes
  // of N * G - B. (Just guesses. May tune that later.)
  const unsigned G = 32;
  const unsigned B = 8;
  size *= sizeof (onedig_t);
  size += B;
  size += G - 1;
  size /= G;
  size *= G;
  size -= B;
  size /= sizeof (onedig_t);
  return size;
}


// Compare unsigned digit strings, returns -1/0/+1.

inline int
digit_cmp (onedig_t const *a, onedig_t const *b, unsigned n)
{
  for (int i = n; --i >= 0; )
    {
      if (a[i] < b[i])
	return -1;
      else if (a[i] > b[i])
	return 1;
    }
  return 0;
}


// Add unsigned digit strings, return carry. Assumes l1 >= l2!
static _fast onedig_t
digit_add (onedig_t const *d1, unsigned l1,
	   onedig_t const *d2, unsigned l2,
	   onedig_t *r)			// May be same as d1 or d2.
{
  twodig_t c = 0;
  unsigned i = 0;
  while (i < l2)
    {
      c += twodig_t (d1[i]) + twodig_t (d2[i]);
      r[i++] = onedig_t (c);
      c >>= single_bits;
    }
  while (i < l1)
    {
      c += twodig_t (d1[i]);
      r[i++] = onedig_t (c);
      c >>= single_bits;
      if (c == 0)
	goto copy;
    }
  return onedig_t (c);
 copy:
  if (r != d1)
    while (i < l1)
      r[i] = d1[i], ++i;
  return 0;
}


// Subtract unsigned digit strings, return carry. Assumes l1 >= l2!
static _fast void
digit_sub (onedig_t const *d1, unsigned l1,
	   onedig_t const *d2, unsigned l2,
	   onedig_t *r)			// May be same as d1 or d2.
{
  twodig_t c = 1;
  unsigned i = 0;
  while (i < l2)
    {
      c += twodig_t (d1[i]) + single_max - twodig_t (d2[i]);
      r[i++] = onedig_t (c);
      c >>= single_bits;
    }
  while (i < l1)
    {
      if (c != 0)
	goto copy;
      c = twodig_t (d1[i]) + single_max;
      r[i++] = onedig_t (c);
      c >>= single_bits;
    }
  return;
 copy:
  if (r != d1)
    while (i < l1)
      r[i] = d1[i], ++i;
}


// Multiply unsigned digit string by single digit, replaces argument
// with product and returns overflowing digit.
static _fast onedig_t
digit_mul (onedig_t *b, unsigned l, onedig_t d)
{
  twodig_t p = 0;
  for (int i = l; --i >= 0; )
    {
      p += twodig_t (d) * twodig_t (*b);
      *b++ = onedig_t (p);
      p >>= single_bits;
    }
  return onedig_t (p);
}


// Multiply two digit strings. Writes result into a third digit string
// which must have the appropriate size and must not be same as one of
// the arguments.
static _fast void
digit_mul (onedig_t const *a, unsigned la,
	   onedig_t const *b, unsigned lb,
	   onedig_t *r)			// Must not be same as a or b.
{
  memset (r, 0, (la + lb) * sizeof (onedig_t));
  for (unsigned i = 0; i < la; i++)
    {
      onedig_t d = a[i];
      twodig_t p = 0;
      for (unsigned j = 0; j < lb; j++)
	{
	  p += r[j] + twodig_t (d) * b[j];
	  r[j] = onedig_t (p);
	  p >>= single_bits;
	}
      r[lb] = onedig_t (p);
      ++r;
    }
}


// Divide unsigned digit string by single digit, replaces argument
// with quotient and returns remainder.
static _fast onedig_t
digit_div (onedig_t *b, unsigned l, onedig_t d)
{
  twodig_t r = 0;
  for (int i = l; --i >= 0; )
    {
      r <<= single_bits;
      r |= b[i];
      b[i] = onedig_t (r / d);
      r %= d;
    }
  return onedig_t (r);
}


// Subroutines for division primitive. Mostly for clarity.

// Guess quotient digit based on the three most significant dividend
// digits and the two most significant digits of the divisor. Since we
// have least significant digit first here, the indices used to access
// less significant digits are negative.
inline onedig_t
guess_q (onedig_t const *r, onedig_t const *y)
{
  onedig_t q = onedig_t (y[0] == r[0]
			 ? single_max
			 : (twodig_t (r[0]) << single_bits | r[-1]) / y[0]);
  for (;;)
    {
      onedig_t t[3];
      twodig_t p;
      p  = twodig_t (q) * y[-1]; t[0] = onedig_t (p); p >>= single_bits;
      p += twodig_t (q) * y[ 0]; t[1] = onedig_t (p); p >>= single_bits;
      t[2] = onedig_t (p);
      if (digit_cmp (t, r - 2, 3) <= 0)
	return q;
      --q;
    }
}

// Multiply divisor with quotient digit and subtract from dividend.
// Returns overflow.
static _fast onedig_t
multiply_and_subtract (onedig_t *r, onedig_t const *y, unsigned l, onedig_t q)
{
  twodig_t p = 0;
  twodig_t h = 1;
  for (unsigned i = 0; i < l; i++)
    {
      p += twodig_t (q) * y[i];
      h += r[i];
      h += single_max;
      h -= onedig_t (p);
      r[i] = onedig_t (h);
      p >>= single_bits;
      h >>= single_bits;
    }
  h += r[l];
  h += single_max;
  h -= p;
  r[l] = onedig_t (h);
  return onedig_t (h >> single_bits);
}

// Add back divisor digits to dividend, corresponds to a correction of
// the guessed quotient digit by -1.
static _fast void
add_back (onedig_t *r, onedig_t const *y, unsigned l)
{
  twodig_t h = 0;
  for (unsigned i = 0; i < l; i++)
    {
      h += r[i];
      h += y[i];
      r[i] = onedig_t (h);
      h >>= single_bits;
    }
  r[l] = 0;
}

// Divide two digit strings. Divides r by y/yl. Stores quotient in
// q/ql and leaves the remainder in r. Size of r is yl+ql.
static _fast void
digit_div (onedig_t *r, const onedig_t *y, unsigned yl, onedig_t *q, unsigned ql)
{
  r += ql;
  for (int i = ql; --r, --i >= 0; )
    {
      onedig_t qh = guess_q (r + yl, y + yl - 1);
      if (multiply_and_subtract (r, y, yl, qh) == 0)
	{
	  --qh;
	  add_back (r, y, yl);
	}
      if (q != 0)
	q[i] = qh;
    }
}


// Newly allocate uninitialized space for specified number of digits.

inline void
BigInt::allocate (unsigned digits)
{
  size = adjust_size (digits);
  length = 0;
  digit = new onedig_t[size];
}


// Used in assignment: When smaller than specified digits, allocate
// anew. Don`t bother to keep the contents.

inline void
BigInt::reallocate (unsigned digits)
{
  if (digits > size)
    {
      if (size)
	delete[] digit;
      size = adjust_size (digits);
      digit = new onedig_t[size];
    }
}


// Increase size keeping the contents.

inline void
BigInt::resize (unsigned digits)
{
  if (digits > size)
    {
      onedig_t *old_digit = digit;
      unsigned old_size = size;
      size = adjust_size (digits);
      digit = new onedig_t[size];
      if (old_digit)
	{
	  memcpy (digit, old_digit, length * sizeof (onedig_t));
	  if (old_size)
	    delete[] old_digit;
	}
    }
}


// Adjust length (e.g. after subtraction).

inline void
BigInt::adjust()
{
  for (; ; --length)
    {
      if (length == 0)
	{
	  positive = true;
	  break;
	}
      if (digit[length - 1] != 0)
	break;
    }
}


// Store unsigned elementary integer type into string of onedig_t.

inline void
digit_set (ullong_t ul, onedig_t d[small], unsigned &l)
{
  l = 0;
  if (ul)
    {
      d[l++] = onedig_t (ul);
      ul >>= single_bits;
      if (small > 2)
	while (ul)
	  {
	    d[l++] = onedig_t (ul);
	    ul >>= single_bits;
	  }
      else
	if (ul)
	  d[l++] = onedig_t (ul);
    }
}

void
BigInt::assign (ullong_t ul)
{
  positive = true;
  digit_set (ul, digit, length);
}

// Dito signed.
void
BigInt::assign (llong_t l)
{
  if (l >= 0)
    {
      digit_set (ullong_t (l), digit, length);
      positive = true;
    }
  else
    {
      digit_set (ullong_t (-l), digit, length);
      positive = false;
    }
}


BigInt::~BigInt()
{
  if (size > 0)
    {
      memset (digit, 0, size * sizeof digit[0]); // Crypto-paranoia.
      delete[] digit;
    }
}

BigInt::BigInt (onedig_t *dig, unsigned len, bool pos)
  : size (0),
    length (len),
    digit (dig),
    positive (pos)
{}

BigInt::BigInt()
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size]),
    positive (true)
{}

BigInt::BigInt (signed long int n)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (llong_t (n));
}

BigInt::BigInt (unsigned long int n)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (ullong_t (n));
}

BigInt::BigInt (int n)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (llong_t (n));
}

BigInt::BigInt (unsigned u)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (ullong_t (u));
}

BigInt::BigInt (llong_t l)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (l);
}

BigInt::BigInt (ullong_t ul)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size])
{
  assign (ul);
}

BigInt::BigInt (BigInt const &y)
  : size (adjust_size (y.length)),
    length (y.length),
    digit (new onedig_t[size]),
    positive (y.positive)
{
  memcpy (digit, y.digit, length * sizeof (onedig_t));
}

BigInt::BigInt (char const *s, onedig_t b)
  : size (adjust_size (small)),
    length (0),
    digit (new onedig_t[size]),
    positive (true)
{
  scan (s, b);
}


BigInt &
BigInt::operator= (llong_t l)
{
  reallocate (small);
  assign (l);
  return *this;
}

BigInt &
BigInt::operator= (ullong_t ul)
{
  reallocate (small);
  assign (ul);
  return *this;
}

BigInt &
BigInt::operator= (BigInt const &y)
{
  if (&y != this)
    {
      reallocate (y.length);
      length = y.length;
      positive = y.positive;
      memcpy (digit, y.digit, length * sizeof (onedig_t));
    }
  return *this;
}

BigInt &
BigInt::operator= (char const *s)
{
  scan (s);
  return *this;
}


char const *
BigInt::scan_on (char const *s, onedig_t b)
{
  for (char c = *s; c; c = *++s)
    {
      // Convert digit. Use 0..9A..Z for singles up to 36. Ignoring case.
      c = toupper (c);
      onedig_t dig;
      if (c < '0')
	return s;
      else if (c <= '9')
	dig = c - '0';
      else if (c < 'A')
	return s;
      else if (c <= 'Z')
	dig = c - 'A' + 10;
      else
	return s;
      if (dig >= b)
	return s;
      // Multiply this by single and add digit.
      onedig_t r = digit_mul (digit, length, b);
      if (r)
	{
	  resize (length + 1);
	  digit[length++] = r;
	}
      if (length == 0)
	// digit_add() would choke on empty first argument.
	length = 1, digit[0] = dig;
      else
	{
	  r = digit_add (digit, length, &dig, 1, digit);
	  if (r)
	    {
	      resize (length + 1);
	      digit[length++] = r;
	    }
	}
    }
  adjust();
  return s;
}

char const *
BigInt::scan (char const *s, onedig_t b)
{
  if (*s == '-')
    positive = false, ++s;
  else if (*s == '+')
    ++s;
  return scan_on (s, b);
}


unsigned
BigInt::digits (onedig_t b) const
{
  int bits = -1;
  while (b)
    ++bits, b >>= 1;
  return (single_bits * length + bits - 1) / bits;
}

char *
BigInt::as_string (char *p, unsigned l, onedig_t b) const
{
  if (l < 2)
    return 0;				// Not enough room for number.
  p[--l] = '\0';
  // Check for zero. Would otherwise print as empty string.
  unsigned len = length;
  while (len && digit[len-1] == 0)
    --len;
  if (len == 0)
    {
      p[--l] = '0';
      return p + l;
    }
  // Make a temporary copy of the digits.
  onedig_t *dig = (onedig_t *)alloca (len * sizeof (onedig_t));
  memcpy (dig, digit, len * sizeof (onedig_t));
  // Divide down by single, generating digits from right to left.
  do
    {
      if (l == 0)
	return 0;
      onedig_t r = digit_div (dig, len, b);
      p[--l] = r < 10 ? r + '0' : 'A' + r - 10;
      if (dig[len-1] == 0)
	--len;
    }
  while (len);
  // Maybe attach sign.
  if (!positive){
    if (l == 0)
      return 0;
    else
      p[--l] = '-';
  }
  // Return pointer to start of number.
  return p + l;
}

bool
BigInt::dump (unsigned char *p, unsigned n)
{
  // Access most significant digit.
  onedig_t *t = digit + length;
  while (t > digit && t[-1] == 0)
    --t;
  if (t <= digit)
    {
      // Number is zero.
      memset (p, 0, n);
      return true;
    }
  // Determine number m of characters needed.
  onedig_t d = *--t;
  unsigned i = sizeof (onedig_t);
  while (--i && (d >> i * CHAR_BIT) == 0);
  unsigned m = ++i + (t - digit) * sizeof (onedig_t);
  // Fill in leading zeroes.
  if (m > n)
    {
      // Number doesn't fit into the provided space, overflow.
      memset (p, 0, n);
      return false;
    }
  memset (p, 0, n - m);
  p += n - m;
  // Copy out digits.
  for (;;)
    {
      while (i--)
	*p++ = d >> i * CHAR_BIT;
      if (t <= digit)
	break;
      d = *--t;
      i = sizeof (onedig_t);
    }
  return true;
}

void
BigInt::load (unsigned char const *p, unsigned n)
{
  // Skip leading zeroes.
  while (n > 0 && *p == 0)
    ++p, --n;
  // Provide enough digits for the assigned number.
  reallocate ((n + sizeof (onedig_t) - 1) / sizeof (onedig_t));
  // Copy in digits.
  length = 0;
  unsigned char const *q = p + n;
  onedig_t d = 0;
  unsigned i = 0;
  for (;;)
    {
      if (q <= p)
	break;
      d |= *--q << i++ * CHAR_BIT;
      if (i < sizeof (onedig_t))
	continue;
      digit[length++] = d;
      d = 0;
      i = 0;
    }
  if (d)
    digit[length++] = d;
}

bool
BigInt::is_long() const
{
  if (length < small)
    return true;
  if (length > small)
    return false;
  const onedig_t max = onedig_t (1) << (single_bits - 1);
  if (digit[small - 1] < max)
    return true;
  if (positive || digit[small - 1] > max)
    return false;
  // There is exactly one good signed number n with abs (n) having the
  // topmost bit set: The most negative number.
  for (int l = length - 1; --l >= 0; )
    if (digit[l] != 0)
      return false;
  return true;
}

ullong_t BigInt::to_ulong() const
{
  ullong_t ul = 0;
  for (int i = length; --i >= 0; )
    {
      ul <<= single_bits;
      ul |= digit[i];
    }
  return ul;
}

llong_t BigInt::to_long() const
{
  ullong_t ul = to_ulong();
  return positive ? ul : -llong_t (ul);
}


// Auxiliary method for comparing magnitude.

inline int
BigInt::ucompare (BigInt const &b) const
{
  if (length < b.length)
    return -1;
  else if (length > b.length)
    return 1;
  else
    return digit_cmp (digit, b.digit, length);
}

// Comparision primitives.

int
BigInt::compare (ullong_t b) const
{
  if (!positive)
    return -1;
  onedig_t dig[small];
  unsigned len;
  digit_set (b, dig, len);
  if (length < len)
    return -1;
  if (length > len)
    return 1;
  else
    return digit_cmp (digit, dig, len);
}

int
BigInt::compare (llong_t b) const
{
  // DK original code:
  // return b < 0 ? -compare (ullong_t (-b)) : compare (ullong_t (b));
  // fails if b is negative

  if(b>=0)
    return compare (ullong_t (b));

  if (positive)
    return 1;

  onedig_t dig[small];
  unsigned len;
  digit_set (-b, dig, len);
  if (length < len)
    return 1;
  if (length > len)
    return -1;
  else
    return -digit_cmp (digit, dig, len);
}

int
BigInt::compare (BigInt const &b) const
{
  if (positive < b.positive)
    return -1;
  else if (positive > b.positive)
    return 1;
  int result = ucompare (b);
  return positive ? result : -result;
}


// Auxiliary method for all adding and subtracting.

void
BigInt::add (onedig_t const *dig, unsigned len, bool pos)
{
  // Make sure the result fits into this, even with carry.
  resize ((length > len ? length : len) + 1);

  // Assign greater operand to d1/l1, for the add/sub primitives
  // expect the greater operand first.
  onedig_t const *d1;
  onedig_t const *d2;
  unsigned l1, l2;
  bool gt = (length > len ||
	     (length == len && digit_cmp (digit, dig, len) >= 0));
  if (gt)
    {
      d1 = digit;
      l1 = length;
      d2 = dig;
      l2 = len;
    }
  else
    {
      d1 = dig;
      l1 = len;
      d2 = digit;
      l2 = length;
    }

  // Decide if the magnitudes are to be added or subtracted.
  if (positive == pos)
    {
      // We're adding effectively.
      onedig_t c = digit_add (d1, l1, d2, l2, digit);
      length = l1;
      if (c)
	digit[length++] = c;
      // Sign remains unchanged.
    }
  else
    {
      // We're subtracting effectively.
      digit_sub (d1, l1, d2, l2, digit);
      length = l1;
      // The greater operand determines the sign of the result.
      if (!gt)
	positive = pos;
      adjust();
    }
}


// Auxiliary method for multiplication.

void
BigInt::mul (onedig_t const *dig, unsigned len, bool pos)
{
  if (len < 2)
    {
      // Handle small dig/len operand efficiently.
      if (len == 0 || dig[0] == 0)
	{
	  length = 0;
	  positive = true;
	  return;
	}
      if (dig[0] != 1)
	{
	  onedig_t c = digit_mul (digit, length, dig[0]);
	  if (c != 0)
	    {
	      resize (length + 1);
	      digit[length++] = c;
	    }
	}
    }
  else if (length < 2)
    {
      // Handle small this efficiently, replacing it with dig/len.
      if (length == 0 || digit[0] == 0)
	{
	  length = 0;
	  positive = true;
	  return;
	}
      onedig_t d = digit[0];
      reallocate (len + 1);
      memcpy (digit, dig, len * sizeof (onedig_t));
      length = len;
      if (d != 1)
	{
	  onedig_t c = digit_mul (digit, length, d);
	  if (c != 0)
	    digit[length++] = c;
	}
    }
  else
    {
      // Get a new string of digits for the result.
      unsigned old_size = size;
      size = adjust_size (length + len);
      onedig_t *r = new onedig_t[size];

      // The first parameter pair defines the outer loop which should
      // be the shorter.
      if (length < len)
	digit_mul (digit, length, dig, len, r);
      else
	digit_mul (dig, len, digit, length, r);

      // Replace digit string of this with result.
      if (old_size)
	delete[] digit;
      digit = r;
      length += len;
      adjust();
    }
  if (!pos)
    positive = !positive;
}


BigInt &
BigInt::operator+= (llong_t y)
{
  bool pos = y > 0;
  ullong_t uy = pos ? y : -y;
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  add (yb, yl, pos);
  return *this;
}

BigInt &
BigInt::operator-= (llong_t y)
{
  bool pos = y > 0;
  ullong_t uy = pos ? y : -y;
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  add (yb, yl, !pos);
  return *this;
}

BigInt &
BigInt::operator*= (llong_t y)
{
  bool pos = y > 0;
  ullong_t uy = pos ? y : -y;
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  mul (yb, yl, pos);
  return *this;
}

BigInt &
BigInt::operator/= (llong_t y)
{
  bool pos = y > 0;
  ullong_t uy = pos ? y : -y;
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  return *this /= BigInt (yb, yl, pos);
}

BigInt &
BigInt::operator%= (llong_t y)
{
  bool pos = y > 0;
  ullong_t uy = pos ? y : -y;
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  return *this %= BigInt (yb, yl, pos);
}


BigInt &
BigInt::operator+= (ullong_t uy)
{
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  add (yb, yl, true);
  return *this;
}

BigInt &
BigInt::operator-= (ullong_t uy)
{
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  add (yb, yl, false);
  return *this;
}

BigInt &
BigInt::operator*= (ullong_t uy)
{
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  mul (yb, yl, true);
  return *this;
}

BigInt &
BigInt::operator/= (ullong_t uy)
{
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  return *this /= BigInt (yb, yl, true);
}

BigInt &
BigInt::operator%= (ullong_t uy)
{
  onedig_t yb[small];
  unsigned yl;
  digit_set (uy, yb, yl);
  return *this %= BigInt (yb, yl, true);
}


BigInt &
BigInt::operator+= (BigInt const &y)
{
  add (y.digit, y.length, y.positive);
  return *this;
}

BigInt &
BigInt::operator-= (BigInt const &y)
{
  add (y.digit, y.length, !y.positive);
  return *this;
}

BigInt &
BigInt::operator*= (BigInt const &y)
{
  mul (y.digit, y.length, y.positive);
  return *this;
}


// Division method returning both quotient and remainder.

void
BigInt::div (BigInt const &x, BigInt const &y, BigInt &q, BigInt &r)
{
  // Eliminate some trivial cases.
  int cmp = x.ucompare (y);
  if (cmp < 0)
    {
      // Dividend less than divisor: Quotient = 0, remainder = dividend.
      r = x;
      q.length = 0;
      q.positive = true;
      return;
    }
  if (cmp == 0)
    {
      // Both operands are equal: Quotient = 1, remainder = 0.
      r.length = 0;
      r.positive = true;
      q.length = 1;
      q.digit[0] = 1;
      if (!y.positive)
	q.negate();
      return;
    }
  if (y.length == 0)
    {
    zero:
      error ("Division by zero.");
      return;
    }
  if (x.is_ulong())
    {
      // Can do it directly.
      ullong_t n = x.to_ulong();
      ullong_t m = y.to_ulong();
      if (m == 0)
	goto zero;
      q.assign (n / m);
      r.assign (n % m);
    }
  else if (y.length == 1)
    {
      // This digit_div() transforms the dividend into the quotient.
      q = y;
      r.digit[0] = digit_div (q.digit, q.length, y.digit[0]);
      r.length = r.digit[0] ? 1 : 0;
    }
  else
    {
      // Copy operands and scale them such that the first divisor
      // digit is initially no less than half base. This is essential
      // for guess_q() to work.
      unsigned al = x.length;
      onedig_t *a = (onedig_t *)alloca ((al + 2) * sizeof (onedig_t));
      memcpy (a, x.digit, al * sizeof (onedig_t));

      unsigned bl = y.length;
      onedig_t *b = (onedig_t *)alloca (bl * sizeof (onedig_t));
      memcpy (b, y.digit, bl * sizeof (onedig_t));

      onedig_t scale = onedig_t (base / (1 + b[bl - 1]));
      if (scale != 1)
	{
	  if ((a[al] = digit_mul (a, al, scale)) != 0) ++al;
	  digit_mul (b, bl, scale);
	}

      // Still we must avoid the first dividend digit being greater
      // than the first divisor digit.
      if (a[al-1] >= b[bl-1])
	a[al++] = 0;

      // Prepare q for receiving the quotient.
      q.length = al - bl;
      q.resize (q.length);

      // Divide.
      digit_div (a, b, bl, q.digit, q.length);

      // Unscale the remainder and copy it into r.
      for (al = bl; al && a[al - 1] == 0; --al);
      if (scale != 1)
	digit_div (a, al, scale);
      if (al && a[al - 1] == 0) --al;
      r.length = al;
      r.resize (r.length);
      memcpy (r.digit, a, al * sizeof (onedig_t));
    }
  q.adjust();
  q.positive = q.length == 0 || x.positive == y.positive;
  r.positive = r.length == 0 || x.positive;
}

BigInt &
BigInt::operator/= (BigInt const &y)
{
  // Eliminate some trivial cases.
  int cmp = ucompare (y);
  if (cmp < 0)
    {
      // Dividend less than divisor: Quotient = 0.
      length = 0;
      positive = true;
      return *this;
    }
  if (cmp == 0)
    {
      // Both operands are equal: Quotient = 1.
      length = 1;
      digit[0] = 1;
      goto set_sign;
    }
  if (y.length == 0)
    {
    zero:
      error ("Division by zero.");
      return *this;
    }
  if (is_ulong())
    {
      // Can do it directly.
      ullong_t n = to_ulong();
      ullong_t m = y.to_ulong();
      if (m == 0)
	goto zero;
      digit_set (n / m, digit, length);
    }
  else if (y.length == 1)
    {
      // This digit_div() transforms the dividend into the quotient.
      digit_div (digit, length, y.digit[0]);
    }
  else
    {
      // Copy and scale as above in div().
      unsigned al = length;
      onedig_t *a = (onedig_t *)alloca ((al + 2) * sizeof (onedig_t));
      memcpy (a, digit, al * sizeof (onedig_t));

      unsigned bl = y.length;
      onedig_t *b = (onedig_t *)alloca (bl * sizeof (onedig_t));
      memcpy (b, y.digit, bl * sizeof (onedig_t));

      onedig_t scale = onedig_t (base / (1 + b[bl - 1]));
      if (scale != 1)
	{
	  if ((a[al] = digit_mul (a, al, scale)) != 0) ++al;
	  digit_mul (b, bl, scale);
	}
      if (a[al-1] >= b[bl-1])
	a[al++] = 0;
      length = al - bl;
      digit_div (a, b, bl, digit, length);
    }
  adjust();
 set_sign:
  if (!y.positive)
    negate();
  return *this;
}

BigInt &
BigInt::operator%= (BigInt const &y)
{
  // Eliminate some trivial cases.
  int cmp = ucompare (y);
  if (cmp < 0)
    {
      // Dividend less than divisor: Remainder = dividend.
      return *this;
    }
  if (cmp == 0)
    {
      // Both operands are equal: Remainder = 0.
      length = 0;
      positive = true;
      return *this;
    }
  if (y.length == 0)
    {
    zero:
      error ("Division by zero.");
      return *this;
    }
  if (is_ulong())
    {
      // Can do it directly.
      ullong_t n = to_ulong();
      ullong_t m = y.to_ulong();
      if (m == 0)
	goto zero;
      digit_set (n % m, digit, length);
    }
  else if (y.length == 1)
    {
      // This digit_div() transforms the dividend into the quotient.
      // Overwrite with remainder immediately afterwards.
      digit[0] = digit_div (digit, length, y.digit[0]);
      length = 1;
    }
  else
    {
      // Scale as above. But do not copy dividend. It is transformed
      // into the remainder which is the result we want here.
      resize (length + 2);
      unsigned &al = length;
      onedig_t *a = digit;

      unsigned bl = y.length;
      onedig_t *b = (onedig_t *)alloca (bl * sizeof (onedig_t));
      memcpy (b, y.digit, bl * sizeof (onedig_t));

      onedig_t scale = onedig_t (base / (1 + b[bl - 1]));
      if (scale != 1)
	{
	  if ((a[al] = digit_mul (a, al, scale)) != 0) ++al;
	  digit_mul (b, bl, scale);
	}
      if (a[al-1] >= b[bl-1])
	a[al++] = 0;
      digit_div (a, b, bl, 0, al - bl);
      length = bl;
      adjust();
      if (scale != 1)
	digit_div (digit, length, scale);
    }
  adjust();
  if (length == 0)
    positive = true;
  return *this;
}
