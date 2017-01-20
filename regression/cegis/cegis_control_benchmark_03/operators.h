/*
 * operators.h
 *
 *  Created on: 18 Jan 2017
 *      Author: elipol
 */

#ifndef OPERATORS_H_
#define OPERATORS_H_

#ifndef INTERVAL
  #define controller_mult(x,y) ((x) *(y))
  #define mult(x,y) ( (x) * (y))

  #define _abs(a) ( (a) < 0 ? -(a) : (a))
  #define add(x,y) ( (x) + (y))

  #define lessthan(x,y) ((x) )< (y))
  #define greaterthan(x,y) ((x)>(y))
  #define lessthanzero(x) ((x) < 0)
  #define lessthan_equaltozero(x) ((x) <= 0)
  #define zero_type 0
  #define one_type (__plant_precisiont)1.0
  #define minusone  (__plant_precisiont)-1
  #define div(x,y) ( (x) / (y))
  #define sub(x,y) ( (x) - (y))
  #define set(x,y) (x)=(y)


#endif
#ifdef INTERVAL

  #define controller_mult(x,y) (interval_fxp_mult((x),(y)))
  #define mult(x,y) ( interval_mult((x),(y)))

  #define _abs(a) ( abs_interval(a))

  #define lessthan(x,y) (interval_lessthan(x,y))
  #define greaterthan(x,y) (interval_greaterthan((x),(y)))
  #define add(x,y) (interval_add((x),(y)))
  #define lessthanzero(x) (interval_lessthanzero(x))
  #define lessthan_equaltozero(x) (interval_lessthan_equal_to_zero(x))

  #define zero_type (zero_interval)
  #define minusone  (minusone_interval)
  #define one_type one_interval
  #define div(x,y) (interval_posDiv((x),(y)))
  #define sub(x,y) (interval_sub((x),(y)))

  #define controller_cast(x) (fxp_interval_check(x))
  #define plant_cast(x) x
  #define set(x,y) (x.low=y, x.high=y)


#endif

#endif /* OPERATORS_H_ */
