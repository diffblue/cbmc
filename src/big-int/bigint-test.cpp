// $Id: bigint-test.cc,v 1.1.1.1 2002-06-13 22:00:30 kroening Exp $

// My own BigInt class, test cases.

#include "bigint.hh"
#include "allocainc.h"

#include <new>
#include <errno.h>
#include <stdio.h>
#include <string.h>


// =====================================================================
// Printing and reading bignums.
// =====================================================================

static void
print (FILE *f, BigInt const &x, unsigned base = 10)
{
  unsigned len = x.digits (base) + 2;
  char *s = x.as_string ((char *)alloca (len), len, base);
  fputs (s, f);
}

static bool
read (FILE *f, BigInt &x, unsigned base = 10)
{
  char buf[4096];
  return 1 == fscanf (f, " %4096[-+0-9a-zA-Z]", buf)
    &&   x.scan (buf, base) == buf + strlen (buf);
}

static void
print (BigInt const &x, unsigned base = 10)
{
  print (stdout, x, base);
}

#if 0
static bool
read (BigInt &x, unsigned base = 10)
{
  return read (stdin, x, base);
}
#endif


// =====================================================================
// Simple tests.
// =====================================================================
// Good when something basic is broken an must be debugged.

static void
run_simple_tests ()
{
  print (BigInt (unsigned (0xFFFFFFFF)));		putchar ('\n');
  print (BigInt (unsigned (0xFFFFFFFF)), 2);		putchar ('\n');
  print (BigInt ("123456789012345678901234567890"));	putchar ('\n');

  print (BigInt ("99999999999999999999999999999999", 10) /
	 BigInt ("999999999999999999999999", 10), 10);	putchar ('\n');
  print (BigInt ("99999999999999999999999999999999", 10) %
	 BigInt ("999999999999999999999999", 10), 10);	putchar ('\n');

  BigInt t (100);
  t -= 300;
  print (t);
  putchar ('\n');

  BigInt r = BigInt (-124) + 124;
  print (r);
  if (BigInt (0) <= r)
    printf ("\nworks ok here\n");

  int j;
  BigInt i (1);
  for (j = 0; j < 1000; j++)
    i += 100000000;
  print (i);
  putchar ('\n');

  for (j = 0; j < 2000; j++)
    i -= 100000000;
  print (i);
  putchar ('\n');

  for (j = 0; j < 1000; j++)
    i += 100000000;
  print (i);
  putchar ('\n');
}


// =====================================================================
// Test cases from the clisp test suite in number.tst.
// =====================================================================

// I took those test cases in number.tst from file
//
//	clisp-1998-09-09/tests/number.tst
//
// in clispsrc.tar.gz. From the README file in that directory:
/*

This directory contains a test suite for testing Common Lisp (CLtL1)
implementations.

In its original version it was built by

    Horst Friedrich, ISST of FhG         <horst.friedrich@isst.fhg.de>
    Ingo Mohr, ISST of FhG               <ingo.mohr@isst.fhg.de>
    Ulrich Kriegel, ISST of FhG          <ulrich.kriegel@isst.fhg.de>
    Windfried Heicking, ISST of FhG      <winfried.heicking@isst.fhg.de>
    Rainer Rosenmueller, ISST of FhG     <rainer.rosenmueller@isst.fhg.de>

at

    Institut für Software- und Systemtechnik der Fraunhofer-Gesellschaft
    (Fraunhofer Institute for Software Engineering and Systems Engineering)
    Kurstraße 33
  D-10117 Berlin
    Germany

for their Common Lisp implementation named XCL.

What you see here is a version adapted to CLISP and AKCL by

    Bruno Haible              <haible@ma2s2.mathematik.uni-karlsruhe.de>
*/

// Actually I have no idea what principles directed the choice of test
// cases and what they are worth. Nevertheless it makes me feel better
// when BigInt comes to the same results as a Common Lisp should. Note
// that Lisp uses a floored divide operator which means that the
// quotient is rounded towards negative infinity. The remainder has to
// be adjusted accordingly.

// Each test is operator op1 op2 result [result2]. Everything is white
// space delimited with line breaks meaning nothing special. Read
// operator and operands, compute, compare with expected result and
// complain if not.

static void
print_err (char const *op,
	   BigInt const &a, BigInt const &b,
	   BigInt const &r, BigInt const &s)
{
  fprintf (stderr, "Error in %s:\n", op);
  print (stderr, a);
  fprintf (stderr, " %s ", op);
  print (stderr, b);
  fputs (" = ", stderr);
  print (stderr, r);
  fputs ("\nShould be: ", stderr);
  print (stderr, s);
  fputs ("\n", stderr);
}

static void
run_clisp_tests (char const *fn)
{
  FILE *f = fopen (fn, "rt");
  if (f == 0)
    {
      fprintf (stderr, "Error opening %s: %s.\n", fn, strerror (errno));
      return;
    }
  for (;;)
    {
      char op[2];
      if (1 != fscanf (f, " %1[-+*/]", op))
	{
	  puts ("\nFine!");
	  if (!feof (f))
	    fprintf (stderr, "Error reading operator from %s.\n", fn);
	  fclose (f);
	  return;
	}
      BigInt a, b, r, er;
      if (!read (f, a) ||
	  !read (f, b) ||
	  !read (f, er))
	{
	  fprintf (stderr, "Error reading number from %s.\n", fn);
	  fclose (f);
	  return;
	}
#if 0
      print(a,10); putchar ('\n');
      print(b,10); putchar ('\n');
      print(er,10); putchar ('\n');
#endif
      switch (op[0])
	{
	case '+':
	  r = a + b;
	  break;
	case '-':
	  r = a - b;
	  break;
	case '*':
	  r = a * b;
	  break;
	case '/':
	  // These lines also have a remainder.
	  BigInt em;
	  if (!read (f, em))
	    {
	      fprintf (stderr, "Error reading number from %s.\n", fn);
	      fclose (f);
	      return;
	    }
	  r = a / b;
	  BigInt m = a % b;
	  // The test-data from the Lisp testsuite are assuming
	  // floored divide. Fix the results accordingly.
	  if (!m.is_zero() && a.is_positive() != b.is_positive())
	    {
	      r -= 1;
	      m += b;
	    }
	  if (r != er)
	    {
	      print_err ("/", a, b, r, er);
	      continue;
	    }
	  if (m != em)
	    {
	      print_err ("%", a, b, m, em);
	      continue;
	    }
	  // Also try the method returning both.
	  BigInt::div (a, b, r, m);
	  // Again, transform to floored divide.
	  if (!m.is_zero() && a.is_positive() != b.is_positive())
	    {
	      r -= 1;
	      m += b;
	    }
	  if (r != er)
	    {
	      print_err ("div", a, b, r, er);
	      continue;
	    }
	  if (m != em)
	    {
	      print_err ("rem", a, b, m, em);
	      continue;
	    }
	  putchar ('.');
	  fflush (stdout);
	  continue;
	}
      if (r != er)
	{
	  print_err (op, a, b, r, er);
	  continue;
	}
      putchar ('.');
      fflush (stdout);
    }
}


// =====================================================================
// Integer roots.
// =====================================================================

static BigInt
sqrt (int n, int dig)
{
  BigInt N (n);
  N *= pow (BigInt (100), dig);
  return sqrt (N);
}

static void
run_sqrt_test ()
{
  print (sqrt (2, 1000));
  putchar ('\n');
}

int
main (int, char *[])
{
  run_simple_tests ();
  run_clisp_tests ("number.tst");
  run_sqrt_test ();
  return 0;
}
