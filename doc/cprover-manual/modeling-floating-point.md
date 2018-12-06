[CPROVER Manual TOC](../../)

## Floating Point

The CPROVER tools support bit-accurate reasoning about IEEE-754
floating-point and fixed-point arithmetic. The C standard contains a
number of areas of implementation-defined behavior with regard to
floating-point arithmetic:

-   CPROVER supports C99 Appendix F, and thus, the `__STD_IEC_559__`
    macro is defined. This means that the C `float` data type maps to
    IEEE 754 `binary32` and `double` maps to `binary64` and operations
    on them are as specified in IEEE 754.

-   `long double` can be configured to be `binary64`, `binary128`
    (quad precision) or a 96 bit type with 15 exponent bits and 80
    significant bits. The last is an approximation of Intel's x87
    extended precision double data type. As the C standard allows a
    implementations a fairly wide set of options for `long double`, it
    is best avoided for both portable code and bit-precise analysis. The
    default is to match the build architecture as closely as possible.

-   In CPROVER, floating-point expressions are evaluated at the 'natural
    precision' (the greatest of the arguments) and not at a
    higher precision. This corresponds to `FLT_EVAL_METHOD` set to `0`.
    Note that this is a different policy to some platforms (see below).

-   Expression contraction (for example, converting `x * y +   c` to
    `fma(x,y,c)`) is not performed. In effect, the `FP_CONTRACT` pragma
    is always off.

-   Constant expressions are evaluated at \`run' time wherever possible
    and so will respect changes in the rounding mode. In effect, the
    `FENV_ACCESS` pragma is always off. Note that floating point
    constants are treated as doubles (unless they are followed by `f`
    when they are float) as specified in the C standard. `goto-cc`
    supports `-fsingle-precision-constant`, which allows
    the (non-standard) treatment of constants as floats.

-   Casts from int to float and float to float make use of the current
    rounding mode. Note that the standard requires that casts from float
    to int use round-to-zero (that is, truncation).

### x86 and Other Platform-specific Issues

Not all platforms have the same implementation-defined behavior as
CPROVER. This can cause mismatches between the verification environment
and the execution environment. If this occurs, check the compiler manual
for the choices listed above. There are two common cases that can cause
these problems: 32-bit x86 code and the use of unsafe optimisations.

Many compilers that target 32-bit x86 platforms employ a different
evaluation method. The extended precision format of the x87 unit is used
for all computations regardless of their native precision. Most of the
time, this results in more accurate results and avoids edge cases.
However, it can result in some obscure and difficult to debug behaviour.
Checking if the `FLT_EVAL_METHOD` macro is non-zero (for these platforms
it will typically be 2), should warn of these problems. Changing the
compiler flags to use the SSE registers will resolve many of them, give
a more standards-compliant platform and will likely perform better. Thus
it is *highly* recommended. Use `-msse2 -mfpmath=sse` to enable this
option for GCC. Visual C++ does not have an option to force the
exclusive use of SSE instructions, but `/arch:SSE2` will pick SSE
instructions "when it \[the compiler\] determines that it is faster to
use the SSE/SSE2 instructions" and is thus better than `/arch:IA32`,
which exclusively uses the x87 unit.

The other common cause of discrepancy between CPROVER results and the
actual platform are the use of unsafe optimizations. Some higher
optimisation levels enable transformations that are unsound with respect
to the IEEE-754 standard. Consult the compiler manual and disable any
optimizations that are described as unsafe (for example, the GCC options
`-ffast-math`). The options `-ffp-contract=off` (which replaces
`-mno-fused-madd`), `-frounding-math` and `-fsignaling-nans` are needed
for GCC to be strictly compliant with IEEE-754.

### Rounding Mode

CPROVER supports the four rounding modes given by IEEE-754 1985; round
to nearest (ties to even), round up, round down, and round towards zero.
By default, round to nearest is used. However, command line options
(`--round-to-zero`, and so on) can be used to override this. If more control
is needed, CPROVER has models of `fesetround` (for POSIX systems) and
`_controlfp` (for Windows), which can be used to change the rounding
mode during program execution. Furthermore, the inline assembly commands
fstcw/fnstcw/fldcw (on x86) can be used.

The rounding mode is stored in the (thread local) variable
`__CPROVER_rounding_mode`, but users are strongly advised not to use
this directly.

### Math Library

CPROVER implements some of `math.h`, including `fabs`, `fpclassify`, and
`signbit`. It has very limited support for elementary functions. Care
must be taken when verifying properties that are dependent on these
functions as the accuracy of implementations can vary considerably. The
C compilers can (and many do) say that the accuracy of these functions
is unknown.

### Fixed-point Arithmetic

CPROVER also has support for fixed-point types. The `--fixedbv` flag
switches `float`, `double`, and `long double` to fixed-point types. The
length of these types is platform specific. The upper half of each type
is the integer component and the lower half is the fractional part.


