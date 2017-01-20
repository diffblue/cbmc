/*
 * control_types.h
 *
 *  Created on: 18 Jan 2017
 *      Author: elipol
 */

#ifndef CONTROL_TYPES_H_
#define CONTROL_TYPES_H_

#ifdef CPROVER
    #ifdef INTERVAL
      typedef   __CPROVER_fixedbv[_CONTROL_FLOAT_WIDTH][_CONTORL_RADIX_WIDTH] __plant_precisiont;
      #include "intervals.h"
      typedef   struct intervalt __plant_typet;
      typedef   __CPROVER_fixedbv[_CONTROL_FLOAT_WIDTH][_CONTORL_RADIX_WIDTH] __controller_precisiont;
      typedef   struct intervalt __controller_typet;
      #define interval(x) interval_cast(x);
    #else
      typedef __CPROVER_fixedbv[_CONTROL_FLOAT_WIDTH][_CONTORL_RADIX_WIDTH] __plant_precisiont;
      typedef __plant_precisiont __plant_typet;
      typedef __CPROVER_fixedbv[INT_BITS+FRAC_BITS][FRAC_BITS] __controller_precisiont;
      typedef  __controller_precisiont __controller_typet;
      #define plant_cast(x) ((__plant_typet)x)
      #define controller_cast(x) ((__controller_typet)x)
      #define interval(x) x
    #endif
#else
   #ifdef INTERVAL
     typedef double __plant_precisiont;
      #include "intervals.h"
     typedef struct intervalt __plant_typet;
     typedef double __controller_precisiont; //fixed point arithmetic is implemented using doubles
     typedef struct intervalt __controller_typet;
     #define interval(x) interval_cast(x)
   #endif
  #ifndef INTERVAL
     typedef double __plant_precisiont;
     typedef __plant_precisiont __plant_typet;
     typedef double __controller_precisiont; //fixed point arithmetic is implemented using doubles
     typedef __controller_precisiont __controller_typet;
     #define interval(x) (x)
     #define plant_cast(x) x
     #define controller_cast(x) x
  #endif
#endif

#endif /* CONTROL_TYPES_H_ */
