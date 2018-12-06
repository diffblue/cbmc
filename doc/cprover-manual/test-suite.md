[CPROVER Manual TOC](../../)

## Test Suite Generation with CBMC

### A Small Tutorial with a Case Study

We assume that CBMC is installed on your system. If not, follow
\ref man_install-cbmc "these instructions".

CBMC can be used to automatically generate test cases that satisfy a
certain [code coverage](https://en.wikipedia.org/wiki/Code_coverage)
criteria. Common coverage criteria include branch coverage, condition
coverage and [Modified Condition/Decision Coverage
(MC/DC)](https://en.wikipedia.org/wiki/Modified_condition/decision_coverage).
Among others, MC/DC is required by several avionics software development
guidelines to ensure adequate testing of safety critical software.
Briefly, in order to satisfy MC/DC, for every conditional statement
containing boolean decisions, each Boolean variable should be evaluated
one time to "true" and one time to "false", in a way that affects the
outcome of the decision.

In the following, we are going to demonstrate how to apply the test
suite generation functionality in CBMC, by means of a case study. The
following program is an excerpt from a real-time embedded benchmark
[PapaBench](https://www.irit.fr/recherches/ARCHI/MARCH/rubrique.php3?id_rubrique=97),
and implements part of a fly-by-wire autopilot for an Unmanned Aerial
Vehicle (UAV). We have adjusted it slightly for our purposes.

The aim of function `climb_pid_run` is to control the vertical climb of
the UAV. Details on the theory behind this operation are documented in
the [wiki](https://wiki.paparazziuav.org/wiki/Theory_of_Operation) for
the Paparazzi UAV project. The behavior of this simple controller,
supposing that the desired speed is 0.5 meters per second, is plotted in
the figure below.

![The pid controller](https://github.com/diffblue/cbmc/raw/develop/doc/assets/pid.png "The pid controller")

```
    01: // CONSTANTS:
    02: #define MAX_CLIMB_SUM_ERR 10
    03: #define MAX_CLIMB 1
    04:
    05: #define CLOCK 16
    06: #define MAX_PPRZ (CLOCK*600)
    07:
    08: #define CLIMB_LEVEL_GAZ 0.31
    09: #define CLIMB_GAZ_OF_CLIMB 0.75
    10: #define CLIMB_PITCH_OF_VZ_PGAIN 0.05
    11: #define CLIMB_PGAIN -0.03
    12: #define CLIMB_IGAIN 0.1
    13:
    14: const float pitch_of_vz_pgain=CLIMB_PITCH_OF_VZ_PGAIN;
    15: const float climb_pgain=CLIMB_PGAIN;
    16: const float climb_igain=CLIMB_IGAIN;
    17: const float nav_pitch=0;
    18:
    19: /** PID function INPUTS */
    20: // The user input: target speed in vertical direction
    21: float desired_climb;
    22: // Vertical speed of the UAV detected by GPS sensor
    23: float estimator_z_dot;
    24:
    25: /** PID function OUTPUTS */
    26: float desired_gaz;
    27: float desired_pitch;
    28:
    29: /** The state variable: accumulated error in the control */
    30: float climb_sum_err=0;
    31:
    32: /** Computes desired_gaz and desired_pitch */
    33: void climb_pid_run()
    34: {
    35:
    36:   float err=estimator_z_dot-desired_climb;
    37:
    38:   float fgaz=climb_pgain*(err+climb_igain*climb_sum_err)+CLIMB_LEVEL_GAZ+CLIMB_GAZ_OF_CLIMB*desired_climb;
    39:
    40:   float pprz=fgaz*MAX_PPRZ;
    41:   desired_gaz=((pprz>=0 && pprz<=MAX_PPRZ) ? pprz : (pprz>MAX_PPRZ ? MAX_PPRZ : 0));
    42:
    43:   /** pitch offset for climb */
    44:   float pitch_of_vz=(desired_climb>0) ? desired_climb*pitch_of_vz_pgain : 0;
    45:   desired_pitch=nav_pitch+pitch_of_vz;
    46:
    47:   climb_sum_err=err+climb_sum_err;
    48:   if (climb_sum_err>MAX_CLIMB_SUM_ERR) climb_sum_err=MAX_CLIMB_SUM_ERR;
    49:   if (climb_sum_err<-MAX_CLIMB_SUM_ERR) climb_sum_err=-MAX_CLIMB_SUM_ERR;
    50:
    51: }
    52:
    53: int main()
    54: {
    55:
    56:   while(1)
    57:   {
    58:     /** Non-deterministic input values */
    59:     desired_climb=nondet_float();
    60:     estimator_z_dot=nondet_float();
    61:
    62:     /** Range of input values */
    63:     __CPROVER_assume(desired_climb>=-MAX_CLIMB && desired_climb<=MAX_CLIMB);
    64:     __CPROVER_assume(estimator_z_dot>=-MAX_CLIMB && estimator_z_dot<=MAX_CLIMB);
    65:
    66:     __CPROVER_input("desired_climb", desired_climb);
    67:     __CPROVER_input("estimator_z_dot", estimator_z_dot);
    68:
    69:     climb_pid_run();
    70:
    71:     __CPROVER_output("desired_gaz", desired_gaz);
    72:     __CPROVER_output("desired_pitch", desired_pitch);
    73:
    74:   }
    75:
    76:   return 0;
    77: }
```

To test the PID controller, we construct a main control loop,
which repeatedly invokes the function `climb_pid_run` (line 69). This
PID function has two input variables: the desired speed `desired_climb`
and the estimated speed `estimated_z_dot`. In the beginning of each loop
iteration, values of the inputs are assigned non-deterministically.
Subsequently, the `__CPROVER_assume` statement in lines 63 and 64
guarantees that both values are bounded within a valid range. The
`__CPROVER_input` and `__CPROVER_output` will help clarify the inputs
and outputs of interest for generating test suites.

To demonstrate the automatic test suite generation in CBMC, we call the
following command:

    cbmc pid.c --cover mcdc --unwind 6 --xml-ui

We'll describe those command line options one by one. The option `--cover mcdc`
specifies the code coverage criterion. There
are four conditional statements in the PID function: in lines 41,
44, 48, and 49. To satisfy MC/DC, the test suite has to meet
multiple requirements. For instance, each conditional statement needs to
evaluate to *true* and *false*. Consider the condition
`"pprz>=0 && pprz<=MAX_PPRZ"` in line 41. CBMC instruments three
coverage goals to control the respective evaluated results of
`"pprz>=0"` and `"pprz<=MAX_PPRZ"`. They
satisfy the MC/DC rules.

    !(pprz >= (float)0) && pprz <= (float)(16 * 600)  id="climb_pid_run.coverage.1"
    pprz >= (float)0 && !(pprz <= (float)(16 * 600))  id="climb_pid_run.coverage.2"
    pprz >= (float)0 && pprz <= (float)(16 * 600)     id="climb_pid_run.coverage.3"

Note that `MAX_PPRZ` is defined as 16 \* 600 in line 06 of the program.

The "id" of each coverage goal is automatically assigned by CBMC. For
every coverage goal, a test suite (if there exists) that satisfies such
a goal is printed out in XML format, as the parameter `--xml-ui` is
given. Multiple coverage goals can share a test suite, when the
corresponding execution of the program satisfies all these goals at the
same time.

In the end, the following test suites are automatically generated for
testing the PID controller. A test suite consists of a sequence of input
parameters that are passed to the PID function `climb_pid_run` at each
loop iteration. For example, Test 1 covers the MC/DC goal with
id="climb\_pid\_run.coverage.1". The complete output from CBMC is in
[pid\_test\_suites.xml](pid_test_suites.xml), where every test suite and
the coverage goals it is for are clearly described.

    Test suite:
    Test 1.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f

    Test 2.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 3.
      (iteration 1) desired_climb=0.000000f, estimator_z_dot=-1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 4.
      (iteration 1) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 3) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 4) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 5) desired_climb=0.000000f, estimator_z_dot=-1.000000f
      (iteration 6) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 5.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 2) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 3) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 4) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 5) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 6) desired_climb=-1.000000f, estimator_z_dot=1.000000f

The option `--unwind 6` unwinds the loop inside the main function body
six times. To achieve complete coverage on all the
instrumented goals in the PID function `climb_pid_run`, the loop must be
unwound enough times. For example, `climb_pid_run` needs to
be called at least six times for evaluating the condition
`climb_sum_err>MAX_CLIMB_SUM_ERR` in line 48 to *true*. This corresponds
to Test 5. To learn more about loop unwinding take a look at [Understanding Loop Unwinding](cbmc-loops.shtml).

In this tutorial, we present the automatic test suite generation
functionality of CBMC, by applying the MC/DC code coverage criterion to
a PID controller case study. In addition to `--cover mcdc`, other
coverage criteria such as `branch`, `decision`, and `path`. are also
available when calling CBMC.

### Coverage Criteria

The table below summarizes the coverage criteria that CBMC supports.

Criterion |Definition
----------|----------
assertion |For every assertion, generate a test that reaches it
location  |For every location, generate a test that reaches it
branch    |Generate a test for every branch outcome
decision  |Generate a test for both outcomes of every Boolean expression that is not an operand of a propositional connective
condition |Generate a test for both outcomes of every Boolean expression
mcdc      |Modified Condition/Decision Coverage (MC/DC)
path      |Bounded path coverage
cover     |Generate a test for every `__CPROVER_cover` statement

