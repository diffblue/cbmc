#define INT_BITS 12
#define FRAC_BITS 12
#include "control_types.h"

#define NSTATES 3
#define NINPUTS 1
#define NOUTPUTS 1
#define INPUT_LOWERBOUND (__plant_typet)-1
#define INPUT_UPPERBOUND (__plant_typet)1
const __plant_typet _controller_A[NSTATES][NSTATES] = { { interval(0.9905),interval(0.075687),interval(0.021033) }, { interval(0.125),interval(0),interval(0) }, { interval(0),interval(0.015625),interval(0) } };
const __plant_typet _controller_B[NSTATES] = { interval(16), interval(0), interval(0) };
