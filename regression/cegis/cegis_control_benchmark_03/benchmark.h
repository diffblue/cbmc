/*
 * benchmark.h
 *
 *  Created on: 18 Jan 2017
 *      Author: elipol
 */

#ifndef BENCHMARK_H_
#define BENCHMARK_H_

#define INT_BITS 8
#define FRAC_BITS 8
#include "control_types.h"

#define NSTATES 3
#define NINPUTS 1
#define NOUTPUTS 1
#define INPUT_UPPERBOUND (__plant_precisiont)1
#define INPUT_LOWERBOUND (__plant_precisiont)-1
const __plant_typet _controller_A[NSTATES][NSTATES] = {{ interval(0.9905),interval(0.075687),interval(0.021033) },
                                                        {interval (0.125),interval(0),interval(0) },
                                                        { interval(0),(0.015625),(0) }};
const __plant_typet _controller_B[NSTATES] = { interval(16), interval(0),interval( 0) };



#endif /* BENCHMARK_H_ */
