/*******************************************************************\

Module: Unit test for big-int

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <string>

#include <big-int/bigint.hh>

// =====================================================================
// Printing and reading bignums.
// =====================================================================

static std::string to_string(BigInt const &x, unsigned base = 10)
{
  const std::size_t len = x.digits(base) + 2;
  std::vector<char> dest(len, 0);
  const char *s = x.as_string(dest.data(), len, base);
  return std::string(s);
}

static bool read(const std::string &input, BigInt &x, unsigned base = 10)
{
  return x.scan(input.c_str(), base) == input.c_str() + input.size();
}

TEST_CASE("arbitrary precision integers", "[core][big-int][bigint]")
{
  // =====================================================================
  // Simple tests.
  // =====================================================================
  // Good when something basic is broken an must be debugged.
  SECTION("simple tests")
  {
    REQUIRE(to_string(BigInt(0xFFFFFFFFu)) == "4294967295");
    REQUIRE(
      to_string(BigInt(0xFFFFFFFFu), 2) == "11111111111111111111111111111111");
    REQUIRE(
      to_string(BigInt("123456789012345678901234567890")) ==
      "123456789012345678901234567890");

    REQUIRE(
      to_string(
        BigInt("99999999999999999999999999999999", 10) /
        BigInt("999999999999999999999999", 10)) == "100000000");
    REQUIRE(
      to_string(
        BigInt("99999999999999999999999999999999", 10) %
        BigInt("999999999999999999999999", 10)) == "99999999");

    BigInt t(100);
    t -= 300;
    REQUIRE(to_string(t) == "-200");

    BigInt r = BigInt(-124) + 124;
    REQUIRE(to_string(r) == "0");
    REQUIRE(BigInt(0) <= r);

    BigInt i(1);
    for(int j = 0; j < 1000; j++)
      i += 100000000;
    REQUIRE(to_string(i) == "100000000001");

    for(int j = 0; j < 2000; j++)
      i -= 100000000;
    REQUIRE(to_string(i) == "-99999999999");

    for(int j = 0; j < 1000; j++)
      i += 100000000;
    REQUIRE(to_string(i) == "1");
  }

  // =====================================================================
  // Test cases from the clisp test suite in number.tst.
  // =====================================================================

  // I took those test cases in number.tst from file
  //
  //  clisp-1998-09-09/tests/number.tst
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
  SECTION("clisp tests")
  {
    const std::vector<std::string> number_tst = {
#include "number.tst"
    };

    for(std::size_t i = 0; i < number_tst.size(); i += 4)
    {
      const std::string op = number_tst[i];
      REQUIRE(!op.empty());

      BigInt a, b, r, er;
      REQUIRE(read(number_tst[i + 1], a));
      REQUIRE(read(number_tst[i + 2], b));
      REQUIRE(read(number_tst[i + 3], er));

      switch(op[0])
      {
      case '+':
        r = a + b;
        REQUIRE(r == er);
        break;
      case '-':
        r = a - b;
        REQUIRE(r == er);
        break;
      case '*':
        r = a * b;
        REQUIRE(r == er);
        break;
      case '/':
      {
        // These lines also have a remainder.
        REQUIRE(i + 4 < number_tst.size());
        BigInt em;
        REQUIRE(read(number_tst[i + 4], em));
        ++i;

        r = a / b;
        BigInt m = a % b;
        // The test-data from the Lisp testsuite are assuming
        // floored divide. Fix the results accordingly.
        if(!m.is_zero() && a.is_positive() != b.is_positive())
        {
          r -= 1;
          m += b;
        }
        REQUIRE(r == er);
        REQUIRE(m == em);

        // Also try the method returning both.
        BigInt::div(a, b, r, m);
        // Again, transform to floored divide.
        if(!m.is_zero() && a.is_positive() != b.is_positive())
        {
          r -= 1;
          m += b;
        }
        REQUIRE(r == er);
        REQUIRE(m == em);
      }
      }
    }
  }

  // =====================================================================
  // Integer roots.
  // =====================================================================
  SECTION("integer roots")
  {
    BigInt N(2);
    N *= pow(BigInt(100), 1000);

    REQUIRE(
      to_string(sqrt(N)) ==
      "141421356237309504880168872420969807856967187537694807317667973799073247"
      "846210703885038753432764157273501384623091229702492483605585073721264412"
      "149709993583141322266592750559275579995050115278206057147010955997160597"
      "027453459686201472851741864088919860955232923048430871432145083976260362"
      "799525140798968725339654633180882964062061525835239505474575028775996172"
      "983557522033753185701135437460340849884716038689997069900481503054402779"
      "031645424782306849293691862158057846311159666871301301561856898723723528"
      "850926486124949771542183342042856860601468247207714358548741556570696776"
      "537202264854470158588016207584749226572260020855844665214583988939443709"
      "265918003113882464681570826301005948587040031864803421948972782906410450"
      "726368813137398552561173220402450912277002269411275736272804957381089675"
      "040183698683684507257993647290607629969413804756548237289971803268024744"
      "206292691248590521810044598421505911202494413417285314781058036033710773"
      "09182869314710171111683916581726889419758716582152128229518488472");
  }

  // =====================================================================
  // Tests for floorPow2
  // =====================================================================
  // Tests floorPow2, pow and setPower2
  SECTION("floorPow2")
  {
    BigInt N;
    BigInt M;

    for(unsigned i = 0; i < 512; ++i)
    {
      unsigned x = 512 - i;
      N = pow(BigInt(2), x);
      M.setPower2(x);

      REQUIRE(N == M);

      REQUIRE(N.floorPow2() == x);

      N -= 1;
      REQUIRE(N.floorPow2() == x - 1);

      N += 2;
      REQUIRE(N.floorPow2() == x);
    }

    N = pow(BigInt(2), 0); // 1
    M.setPower2(0);

    REQUIRE(N == M);

    REQUIRE(N.floorPow2() == 0);

    N -= 1; // 0
    REQUIRE(N.floorPow2() == 0);

    N += 2; // 2
    REQUIRE(N.floorPow2() == 1);
  }
}
