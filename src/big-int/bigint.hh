// $Id: bigint.hh,v 1.12 2009-01-24 15:14:46 kroening Exp $

// My own BigInt class, declaration.

#ifndef BIGINT_HH
#define BIGINT_HH

// This one is pretty simple but has a fair divide implementation.
// Though I'm not ambitious enough to do that FFT-like stuff.
//
// Desirable properties / design goals:
//
//  - Highly configurable, should run on chips from 8 to 64 bits word size.
//  - Is relatively small.
//  - Is thread safe.
//  - Does not significantly pollute the global namespace.
//
// Deliberate omissions:
//
//  - Support of the C++ iostream classes which I find obsolete.
//    (Of course there are conversions from/to strings.)
//  - Bitwise operations. A bitset is a different thing than a BigInt.
//
// Porting and configuration:
//
//  - Somehow resolve the problem when your compiler has no `bool' yet.
//  - Choose appropriate elementary types to use for onedig_t, twodig_t,
//    llong_t, and ullong_t. Some possible variants are #ifdef'd below.
//  - Decide what to do on division by zero (in implementation file.)
//  - In allocainc.h, do whatever necessary to provide the alloca() function.
//
// That should be all. I saw this running on:
//
//  - Linux/egcs-1.1.2 ... gcc-2.95.2
//  - Linux/Comeau C++ 4.2.42
//  - Linux/Fujitsu C++
//  - FreeBSD 3.1/gcc-2.7.2 ... 4.1/gcc-2.95.2, NetBSD 1.4.2/egcs-1.1.1
//  - FreeBSD 4.x/TenDRA 4.2-BETA
//  - AIX/xlC
//  - Sun Solaris 2.5 ... 8/Sparc/SunPRO CC 4.2 ... Forte 6.0
//  - Windows NT/i386/MS Visual-C 4.2 ... 6.0
//  - Windows NT/i386/Borland-C++ 5.0, 5.5 (also with Intel reference compiler)
//  - DEC-OSF1/DEC CXX 6.0
//  - DEC OpenVMS 6.2/VAX/DEC CXX 5.5 (without optimization)
//  - DEC OpenVMS 6.2 and 7.1/Alpha/DEC CXX 5.6
//
// Legal status:
//
// The copyright at this source is owned by Dirk Zoller,
// e-mail: duz@sol-3.de
//
// You may however use and modify this without restriction.


// Add your losing compiler to this list.
#if !defined bool						\
     && (defined __SUNPRO_CC && (__SUNPRO_CC < 0x500 ||		\
				 __SUNPRO_CC_COMPAT < 5) ||	\
	 defined __xlC__ ||					\
	 defined __DECCXX && __DECCXX_VER < 60000000 ||		\
	 defined _MSC_VER && _MSC_VER < 1100)
#undef bool
#undef false
#undef true
#define bool int
#define false 0
#define true 1
#endif

// Minor optimization for gcc on some intel platforms.
#if !defined _fast
# if defined __GNUC__ && defined __i386__ && defined NDEBUG
#  define _fast __attribute__ ((__regparm__ (3),__stdcall__))
#  if defined _WIN32
#   define _fasta			// Mingw-gcc crashes when alloca is used
#  else					// inside a function declared regparm
#   define _fasta _fast			// or stdcall (don't know which).
#  endif
# else
#  define _fast
#  define _fasta
# endif
#endif


class BigInt
{
public:
  // Decide about and publish configuration details:

  // Choose digit type for best performance. Bigger is better as long
  // as there are machine instructions for multiplying and dividing on
  // twice the size of a digit, i.e. on twodig_t.
#if defined __GNUG__ || defined __alpha// || defined __TenDRA__
  // Or other true 64 bit CPU.
  typedef unsigned		onedig_t;
  typedef unsigned long long	twodig_t;
#elif defined _MSC_VER // || defined __BORLANDC__ (works but is slower)
  // Like GCC's long long this __int64 actually performs better than
  // unsigned. Though not as much as is the case with gcc.
  typedef unsigned		onedig_t;
  typedef unsigned __int64	twodig_t;
#elif 1
  // Majority (currently) of 32 bit CPUs.
  typedef unsigned short	onedig_t;
  typedef unsigned		twodig_t;
#else
  // Works on 8/16 bit CPUs just as well.
  typedef unsigned char		onedig_t;
  typedef unsigned short	twodig_t;
#endif

  // Choose largest integral type to use. Must be >= twodig_t.
#if defined __GNUG__
  typedef          long long	 llong_t;
  typedef unsigned long long	ullong_t;
#elif defined _MSC_VER// || defined __BORLANDC__
  typedef          __int64	 llong_t;
  typedef unsigned __int64	ullong_t;
#else
  typedef          long		 llong_t;
  typedef unsigned long		ullong_t;
#endif

  // Maximum number of onedig_t digits which could also be represented
  // by an elementary type.
  enum { small = sizeof (ullong_t) / sizeof (onedig_t) };

private:
  unsigned size;			// Length of digit vector.
  unsigned length;			// Used places in digit vector.
  onedig_t *digit;			// Least significant first.
  bool positive;			// Signed magnitude representation.

  // Create or resize this.
  inline void allocate (unsigned digits);
  inline void reallocate (unsigned digits);
  inline void resize (unsigned digits);

  // Adjust length (e.g. after subtraction).
  inline void adjust();

  // Assign to this.
  void assign (llong_t) _fast;
  void assign (ullong_t) _fast;

  // Aux methods, only for internal use.
  inline int ucompare (BigInt const &) const;
  void add (onedig_t const *, unsigned, bool) _fast;
  void mul (onedig_t const *, unsigned, bool) _fast;

  // Auxiliary constructor used for temporary or static BigInt.
  // Sets size=0 which indicates that ~BigInt must not delete[].
  inline BigInt (onedig_t *, unsigned, bool) _fast;

public:
  ~BigInt() _fast;

  BigInt() _fast;
  BigInt (int) _fast;
  BigInt (unsigned) _fast;

  BigInt (long signed int x) _fast;
  BigInt (long unsigned int x) _fast;

  BigInt (llong_t) _fast;
  BigInt (ullong_t) _fast;
  BigInt (BigInt const &) _fast;
  BigInt (char const *, onedig_t = 10) _fast;

  BigInt &operator= (llong_t) _fast;
  BigInt &operator= (ullong_t) _fast;
  BigInt &operator= (BigInt const &) _fast;
  BigInt &operator= (char const *) _fast;

  // Input conversion from text.

  char const *scan_on (char const *, onedig_t = 10) _fast;
  char const *scan    (char const *, onedig_t = 10) _fast;

  // Output conversion into text.

  // Return an upper bound for the number of digits the textual
  // representation of this might have.
  unsigned digits (onedig_t = 10) const _fast;

  // Convert into string, right adjusted in field of specified width.
  // Returns pointer to start of number or NULL if field too small.
  char *as_string (char *, unsigned, onedig_t = 10) const _fasta;

  // Convert to/from a binary representation.

  // Write and read in a compact byte-wise binary form. Effectively
  // print in base 256 with the most significant digit first. Also
  // read back from such a representation. Return success.
  bool dump (unsigned char *, unsigned) _fast;
  void load (unsigned char const *, unsigned) _fast;

  // Conversions to elementary types.

  bool is_long() const _fast;
  bool is_ulong() const			{ return length <= small; }

  // disabled by DK: makes operators ambigous
  //operator llong_t() const _fast;
  //operator ullong_t() const _fast;
  llong_t to_long() const _fast;
  ullong_t to_ulong() const _fast;

#ifndef bool
  // Like int: non-zero is true. Equivalent to !is_zero().
  //operator bool() const			{ return length != 0; }
#endif

  // All comparisions are done with these primitives.

  int compare (llong_t) const _fast;
  int compare (ullong_t) const _fast;
  int compare (BigInt const &) const _fast;

  // Eliminate need for explicit casts when comparing.

  int compare (int n) const		{ return compare (llong_t (n)); }
  int compare (unsigned n) const	{ return compare (ullong_t (n)); }

  // Tests. These are faster than comparing with 0 or of course %2.

  bool is_zero() const			{ return length == 0; }
  bool is_positive() const		{ return positive; }
  bool is_negative() const		{ return !positive; }
  bool is_odd() const			{ return length != 0 && digit[0] & 1; }
  bool is_even() const			{ return !is_odd(); }

  // Arithmetic.

  BigInt &negate()			{ if(!is_zero()) positive = !positive; return *this; }
  BigInt operator-() const		{ return BigInt (*this).negate(); }

  BigInt &operator+= (llong_t) _fast;
  BigInt &operator-= (llong_t) _fast;
  BigInt &operator*= (llong_t) _fast;
  BigInt &operator/= (llong_t) _fast;
  BigInt &operator%= (llong_t) _fast;

  BigInt &operator+= (unsigned long x) { return (*this)+=(ullong_t)x; }
  BigInt &operator-= (unsigned long x) { return (*this)-=(ullong_t)x; }
  BigInt &operator*= (unsigned long x) { return (*this)*=(ullong_t)x; }
  BigInt &operator/= (unsigned long x) { return (*this)/=(ullong_t)x; }
  BigInt &operator%= (unsigned long x) { return (*this)%=(ullong_t)x; }

  BigInt &operator+= (ullong_t) _fast;
  BigInt &operator-= (ullong_t) _fast;
  BigInt &operator*= (ullong_t) _fast;
  BigInt &operator/= (ullong_t) _fast;
  BigInt &operator%= (ullong_t) _fast;

  BigInt &operator+= (BigInt const &) _fast;
  BigInt &operator-= (BigInt const &) _fast;
  BigInt &operator*= (BigInt const &) _fast;
  BigInt &operator/= (BigInt const &) _fasta;
  BigInt &operator%= (BigInt const &) _fasta;

  BigInt &operator++ ()	{ return operator+=(1); } // preincrement
  BigInt &operator-- ()	{ return operator-=(1); } // predecrement

  static void div (BigInt const &, BigInt const &,
		   BigInt &quot, BigInt &rem) _fasta;

  // Avoid the need for explicit casts to [u]llong_t.

  // disabled by DK
  //operator int() const		{ return int (operator llong_t()); }
  //operator unsigned() const	{ return unsigned (operator ullong_t()); }

  BigInt &operator = (int n)		{ return operator = (llong_t (n)); }
  BigInt &operator+= (int n)		{ return operator+= (llong_t (n)); }
  BigInt &operator-= (int n)		{ return operator-= (llong_t (n)); }
  BigInt &operator*= (int n)		{ return operator*= (llong_t (n)); }
  BigInt &operator/= (int n)		{ return operator/= (llong_t (n)); }
  BigInt &operator%= (int n)		{ return operator%= (llong_t (n)); }

  BigInt &operator = (unsigned n)	{ return operator = (ullong_t (n)); }
  BigInt &operator+= (unsigned n)	{ return operator+= (ullong_t (n)); }
  BigInt &operator-= (unsigned n)	{ return operator-= (ullong_t (n)); }
  BigInt &operator*= (unsigned n)	{ return operator*= (ullong_t (n)); }
  BigInt &operator/= (unsigned n)	{ return operator/= (ullong_t (n)); }
  BigInt &operator%= (unsigned n)	{ return operator%= (ullong_t (n)); }

  // Binary arithmetic operators. These are entirely syntactic sugar.
  // Though there's joy in repetition -- let the preprocessor enjoy.

#define decl_binary(T)							\
  BigInt operator+ (T b) const		{ return BigInt (*this) += b; }	\
  BigInt operator- (T b) const		{ return BigInt (*this) -= b; }	\
  BigInt operator* (T b) const		{ return BigInt (*this) *= b; }	\
  BigInt operator/ (T b) const		{ return BigInt (*this) /= b; }	\
  BigInt operator% (T b) const		{ return BigInt (*this) %= b; }
  decl_binary (int);
  decl_binary (unsigned);
  decl_binary (llong_t);
  decl_binary (ullong_t);
  decl_binary (BigInt const &);
#undef decl_binary

  BigInt operator+ (unsigned long b) const	{ return BigInt (*this) += (ullong_t)b; }	\
  BigInt operator- (unsigned long b) const	{ return BigInt (*this) -= (ullong_t)b; }	\
  BigInt operator* (unsigned long b) const	{ return BigInt (*this) *= (ullong_t)b; }	\
  BigInt operator/ (unsigned long b) const	{ return BigInt (*this) /= (ullong_t)b; }	\
  BigInt operator% (unsigned long b) const	{ return BigInt (*this) %= (ullong_t)b; }

  // Binary comparision operators.

#define decl_binary(T)							\
  bool operator<  (T b) const		{ return compare (b) < 0; }	\
  bool operator>  (T b) const		{ return compare (b) > 0; }	\
  bool operator<= (T b) const		{ return compare (b) <= 0; }	\
  bool operator>= (T b) const		{ return compare (b) >= 0; }	\
  bool operator== (T b) const		{ return compare (b) == 0; }	\
  bool operator!= (T b) const		{ return compare (b) != 0; }
  decl_binary (int);
  decl_binary (unsigned);
  decl_binary (llong_t);
  decl_binary (ullong_t);
  decl_binary (BigInt const &);
#undef decl_binary

  bool operator<  (unsigned long b) const	{ return compare ((ullong_t)b) < 0; }	\
  bool operator>  (unsigned long b) const	{ return compare ((ullong_t)b) > 0; }	\
  bool operator<= (unsigned long b) const	{ return compare ((ullong_t)b) <= 0; }	\
  bool operator>= (unsigned long b) const	{ return compare ((ullong_t)b) >= 0; }	\
  bool operator== (unsigned long b) const	{ return compare ((ullong_t)b) == 0; }	\
  bool operator!= (unsigned long b) const	{ return compare ((ullong_t)b) != 0; }
};


// Functions on BigInt. Implementations in bigint-func.cc.

BigInt pow (BigInt const &, unsigned) _fast;
BigInt pow (BigInt const &, BigInt const &, BigInt const &modulus) _fast;
BigInt sqrt (BigInt const &) _fast;
BigInt gcd (const BigInt &, const BigInt &) _fast;
BigInt modinv (const BigInt &, const BigInt &) _fast;


#endif//ndef BIGINT_HH
