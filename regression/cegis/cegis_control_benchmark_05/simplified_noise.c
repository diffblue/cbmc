#include <assert.h>
#include <stdbool.h>

/*#define __CONTROLLER_DEN_SIZE 3
#define __CONTROLLER_NUM_SIZE 3
#define __PLANT_DEN_SIZE 2
#define __PLANT_NUM_SIZE 1
#define SOLUTION_DEN_SIZE 3
#define SOLUTION_NUM_SIZE 3*/
#include "sizes.h"
#define __OPENLOOP_DEN_SIZE (__CONTROLLER_DEN_SIZE+__PLANT_DEN_SIZE-1)
#define __OPENLOOP_NUM_SIZE (__CONTROLLER_NUM_SIZE+__PLANT_NUM_SIZE-1)

#define __NORMALIZED
#ifdef __CPROVER
#ifndef _FIXEDBV
  #ifndef _EXPONENT_WIDTH
    #define _EXPONENT_WIDTH 16
  #endif
  #ifndef _FRACTION_WIDTH
  #define _FRACTION_WIDTH 11
  #endif
  typedef __CPROVER_floatbv[_EXPONENT_WIDTH][_FRACTION_WIDTH] control_floatt;
  control_floatt _imp_max=(((1 <<(_EXPONENT_WIDTH-1))-1)<<1)+1;
#else
  #ifndef _CONTROL_FLOAT_WIDTH
    #define _CONTROL_FLOAT_WIDTH 16
  #endif
  #ifndef _CONTORL_RADIX_WIDTH
    #define _CONTORL_RADIX_WIDTH _CONTROL_FLOAT_WIDTH / 2
  #endif
  typedef __CPROVER_fixedbv[_CONTROL_FLOAT_WIDTH][_CONTORL_RADIX_WIDTH] control_floatt;
  control_floatt _imp_max=(((1 <<(_CONTROL_FLOAT_WIDTH-1))-1)<<1)+1;
#endif
  typedef unsigned char cnttype;
#else
  typedef double control_floatt;
  typedef unsigned int cnttype;
  #include <stdlib.h>
  #include <stdio.h>
#endif

struct anonymous0
{
  cnttype int_bits;
  cnttype frac_bits;
};

struct anonymous3
{
  control_floatt den[SOLUTION_DEN_SIZE];
  control_floatt den_uncertainty[SOLUTION_DEN_SIZE];
  cnttype den_size;
  control_floatt num[SOLUTION_NUM_SIZE];
  control_floatt num_uncertainty[SOLUTION_NUM_SIZE];
  cnttype num_size;
};

control_floatt _dbl_max;
control_floatt _dbl_min;
signed long int _fxp_max;
signed long int _fxp_min;
signed long int _fxp_one;
control_floatt _dbl_lsb;
control_floatt _poly_error;
control_floatt _sum_error;
control_floatt _plant_norm;

struct anonymous0 impl={ .int_bits=_CONTROLER_INT_BITS, .frac_bits=_CONTROLER_FRAC_BITS};

#include "plant.h"
/*struct anonymous3 plant={ .den={ 1.0, -9.998000e-1, 0.0}, .den_uncertainty={0.0, 0.0, 0.0}, .den_size=2,
.num={ 2.640000e-2, 0.0, 0.0}, .num_uncertainty={0.0, 0.0, 0.0}, .num_size=1};*/
/*struct anonymous3 plant={ .den={ 1.0, -3.32481248817168, 1.64872127070013 }, .den_size=3,
    .num={ 0.548693198268086, -0.886738807003861, 0.0 }, .num_size=2};*/

struct anonymous3 plant_cbmc,controller_cbmc;
//#ifdef __CPROVER
#include "controller.h"
//extern struct anonymous3 controller;
/*#else
//struct anonymous3 controller = { .den={ 32218.8125, 3544.125, 29723.25 }, .den_uncertainty={0.0, 0.0, 0.0}, .den_size=3,
// .num={ 17509.4375, 7878.25, 12107.6875 }, .num_uncertainty={0.0, 0.0, 0.0}, .num_size=3};
struct anonymous3 controller = { .den={ 25868.375, -12550.9375, 5127.375 },.den_uncertainty={0.0, 0.0, 0.0}, .den_size=3,
 .num={ 26097, -303.0625, -23076.25 }, .num_uncertainty={0.0, 0.0, 0.0}, .num_size=3};
#endif*/

void __DSVERIFIER_assume(_Bool expression)
{
#ifdef __CPROVER
  __CPROVER_assume(expression != (_Bool)0);
#endif
}

void __DSVERIFIER_assert(_Bool expression)
{
  /* assertion expression */
  assert(expression != (_Bool)0);
}

void initialization()
{
  __DSVERIFIER_assert(impl.int_bits+impl.frac_bits < 32);
#ifdef __NORMALIZED
  _fxp_one = 1 << (impl.frac_bits + impl.int_bits);
  _dbl_lsb=1.0/(1 << impl.frac_bits + impl.int_bits);
  _fxp_min = -(1 << (impl.frac_bits + impl.int_bits -1));
  _fxp_max = (1 << (impl.frac_bits + impl.int_bits-1))-1;
  _dbl_max = (1.0-_dbl_lsb);//Fractional part
#else
  if(impl.frac_bits >= 31)
    _fxp_one = 2147483647l;
  else
    _fxp_one = (1 << impl.frac_bits);
  _dbl_lsb=1.0/(1 << impl.frac_bits);
  _fxp_min = -(1 << (impl.frac_bits + impl.int_bits -1));
  _fxp_max = (1 << (impl.frac_bits + impl.int_bits-1))-1;
  _dbl_max = (1 << (impl.int_bits-1))-1;//Integer part
  _dbl_max += (1.0-_dbl_lsb);//Fractional part
#endif
  _dbl_min = -_dbl_max;
#ifdef __CHECK_FP
  if (SOLUTION_DEN_SIZE>SOLUTION_NUM_SIZE)
  {
    _poly_error=2*_dbl_lsb*SOLUTION_DEN_SIZE;
    _sum_error=2*_poly_error*SOLUTION_DEN_SIZE;
  }
  else
  {
    _poly_error=2*_dbl_lsb*SOLUTION_NUM_SIZE;
    _sum_error=2*_poly_error*SOLUTION_DEN_SIZE;
  }
#else
  _poly_error=0;
  _sum_error=0;
#endif
}

int validation()
{
  cnttype i;
  control_floatt max=0;
  for (i=0;i<plant.num_size;i++) {
    if (plant.num[i]>max) max=plant.num[i];
    else if (-plant.num[i]>max) max=-plant.num[i];
  }
  for (i=0;i<plant.den_size;i++) {
    if (plant.den[i]>max) max=plant.den[i];
    else if (-plant.den[i]>max) max=-plant.den[i];
  }
  unsigned int max_int=max;
#ifdef __NORMALIZED
  cnttype mult_bits=1;
#else
  cnttype mult_bits=12;
#endif
  while (max_int>0)
  {
    mult_bits++;
    max_int>>=1;
  }
  _plant_norm=1<<mult_bits;
#ifdef __CPROVER
  #ifndef _FIXEDBV
    #ifdef __NORMALIZED
      __DSVERIFIER_assert((impl.int_bits+impl.frac_bits<=_FRACTION_WIDTH) && (mult_bits<_EXPONENT_WIDTH));
    #else
      __DSVERIFIER_assert((impl.frac_bits<=_FRACTION_WIDTH) && (impl.int_bits+mult_bits<_EXPONENT_WIDTH));
    #endif
  #else
    #ifdef __NORMALIZED
      __DSVERIFIER_assert((impl.int_bits+impl.frac_bits<=_CONTORL_RADIX_WIDTH) && (mult_bits<_CONTROL_FLOAT_WIDTH));
    #else
      __DSVERIFIER_assert((impl.frac_bits<=_CONTORL_RADIX_WIDTH) && (impl.int_bits+mult_bits<_CONTROL_FLOAT_WIDTH));
    #endif
  #endif
  __DSVERIFIER_assert((__CONTROLLER_DEN_SIZE == controller.den_size) && (__CONTROLLER_NUM_SIZE == controller.num_size) && (plant.num_size != 0) && (impl.int_bits != 0));
#else
  if (!((__CONTROLLER_DEN_SIZE == controller.den_size) && (__CONTROLLER_NUM_SIZE == controller.num_size) && (plant.num_size != 0) && (impl.int_bits != 0))) return 10;
#endif
  for( i=0; i < __CONTROLLER_DEN_SIZE; i++)
  {
    const control_floatt value=controller.den[i];
#ifdef __CPROVER
    __DSVERIFIER_assume(value <= _dbl_max);
    __DSVERIFIER_assume(value >= _dbl_min);
#else
    printf("value=%f", value);
    if(value > _dbl_max) return 10;
    if(value < _dbl_min) return 10;
#endif
  }
  for(i = 0 ; i < __CONTROLLER_NUM_SIZE; i++)
  {
    const control_floatt value=controller.num[i];
#ifdef __CPROVER
    __DSVERIFIER_assume(value <= _dbl_max);
    __DSVERIFIER_assume(value >= _dbl_min);
#else
    if (value > _dbl_max) return 10;
    if (value < _dbl_min) return 10;
#endif
  }
  return 0;
}

#ifndef __CPROVER
void print_poly(control_floatt *pol,cnttype n)
{
  cnttype i;
  for (i=0;i<n;i++)
  {
    printf("%fz%d ", pol[i], n-i-1);
    //std::cout << pol[i] << "z" << n-i-1 << " ";
  }
  puts("");
  //std::cout << std::endl;
}
#endif


#ifdef __CPROVER
control_floatt nondet_double();
#else
control_floatt nondet_double()
{
  return 0;
}
#endif

void call_closedloop_verification_task()
{
  cnttype i=0;
  plant_cbmc.num_size=plant.num_size;
  for(i = 0;i < plant.num_size; i++)
#ifdef __CPROVER
    if(plant.num_uncertainty[i] > 0.0)
    {
      control_floatt factor=(plant.num[i] * plant.num_uncertainty[i]) / 100.0;
      factor = factor < 0.0 ? -factor : factor;
      control_floatt min=plant.num[i] -factor;
      control_floatt max=plant.num[i] +factor;
      plant_cbmc.num[i] = nondet_double();
      __DSVERIFIER_assume(plant_cbmc.num[i] >= min);
      __DSVERIFIER_assume(plant_cbmc.num[i] <= max);
#ifdef __NORMALIZED
      plant_cbmc.num[i]/=_plant_norm;
#endif
    }
    else
#endif
#ifdef __NORMALIZED
      plant_cbmc.num[i] = plant.num[i]/_plant_norm;
#else
      plant_cbmc.num[i] = plant.num[i];
#endif
  plant_cbmc.den_size=plant.den_size;
  for(i = 0; i < plant.den_size; i++)
#ifdef __CPROVER
    if(plant.den_uncertainty[i] > 0.0)
    {
      control_floatt factor=(plant.den[i] * plant.den_uncertainty[i]) / 100.0;
      factor = factor < 0.000000 ? -factor : factor;
      control_floatt min=plant.den[i] -factor;
      control_floatt max=plant.den[i] +factor;
      plant_cbmc.den[i] = nondet_double();
      __DSVERIFIER_assume(plant_cbmc.den[i] >= min);
      __DSVERIFIER_assume(plant_cbmc.den[i] <= max);
#ifdef __NORMALIZED
      plant_cbmc.den[i]/=_plant_norm;
#endif
    }
    else
#endif
#ifdef __NORMALIZED
      plant_cbmc.den[i] = plant.den[i]/_plant_norm;
#else
      plant_cbmc.den[i] = plant.den[i];
#endif
}

int assert_nonzero_controller(void)
{
  unsigned int zero_count = 0;
  for(unsigned int i=0; i < __CONTROLLER_DEN_SIZE; i++)
    if (controller.den[i] == 0.0) ++zero_count;
#ifdef __CPROVER
  __DSVERIFIER_assert(zero_count < __CONTROLLER_DEN_SIZE);
#else
  if (zero_count >= __CONTROLLER_DEN_SIZE) return 0;
#endif
  zero_count = 0;
  for(unsigned int i = 0 ; i < __CONTROLLER_NUM_SIZE; i++)
    if (controller.num[i] == 0.0) ++zero_count;
#ifdef __CPROVER
  __DSVERIFIER_assert(zero_count < __CONTROLLER_NUM_SIZE);
#else
  if (zero_count >= __CONTROLLER_NUM_SIZE) return 0;
#endif
  return 1;
}

signed int check_stability_closedloop(control_floatt *a, cnttype n)
{
  cnttype columns=n;
  control_floatt m[n][n];
  cnttype i;
  cnttype j;
  control_floatt sum=0.0;
  for(i = 0 ; i < n; i++) { sum += a[i]; }
#ifdef __CPROVER
  __DSVERIFIER_assert(a[0] > _poly_error);
  __DSVERIFIER_assert(sum > _sum_error);
  __DSVERIFIER_assert(a[n-1]+_poly_error < a[0]);
  __DSVERIFIER_assert(-a[n-1]+_poly_error < a[0]);
#else
  printf("m[0]=%f>0\n", a[0]);
  //std::cout << "m[0]=" << a[0] << ">0" << std::endl;
  printf("fabs(m[%d]=%f)<m[0]=%f\n", n-1, a[n-1], a[0]);
  //std::cout << "fabs(m[" << n-1 << "]=" << a[n-1] << ")<" << "m[0]=" << a[0] << std::endl;
  printf("sum=%f>0\n", sum);
  //std::cout << "sum=" << sum << ">0" << std::endl;
  if (!(a[0] > _poly_error)) return 0;
  if (!(sum > _sum_error)) return 0;
  if (!(a[n - 1]+_poly_error < a[0])) return 0;
  if (!(-a[n - 1]+_poly_error < a[0])) return 0;
#endif
  sum = 0.0;
  for(i = 0 ; i < n; i++)
  {
    if (((n -i)&1)!=0) sum+=a[i];
    else               sum-=a[i];
  }
  if ((n&1)==0) sum=-sum;
#ifdef __CPROVER
  __DSVERIFIER_assert(sum > _sum_error);
#else
  printf("sumEven-sumOdd=%f>0\n", sum);
  //std::cout << "sumEven-sumOdd=" << sum << ">0" << std::endl;
  if (!(sum > _sum_error)) return 0;
#endif
  for(j=0;j<columns;j++) m[0][j]=a[j];
  columns--;
  control_floatt error=_poly_error;
  control_floatt mag=1;
  for(i=1;i<n;i++)
  {
    //denominator is always >0
    __DSVERIFIER_assert(m[i-1][0] > 0.0);
    control_floatt factor=m[i-1][columns] / m[i-1][0];
#ifdef __CHECK_FP
    if (m[i-1][0]<0) __DSVERIFIER_assert(m[i-1][0]<-(mag*mag/_imp_max+_poly_error));
    else             __DSVERIFIER_assert(m[i-1][0]> (mag*mag/_imp_max+_poly_error));//check for overflow.
    control_floatt efactor=m[i-1][columns];
    if (efactor<0) efactor=-efactor;
    efactor+=_poly_error;
    efactor/=m[i-1][0]-_poly_error;
    efactor-=factor;
    __DSVERIFIER_assert(efactor<_poly_error*mag);
    if (factor>0)
    {
      _poly_error*=2+factor;//Unsound! does not consider the error in factor (a+e/b-e = a/(b-e) +e/(b-e))
      mag+=mag*factor;
    }
    else
    {
      _poly_error*=2-factor;
      mag-=mag*factor;
    }
#endif
    for(j=0;j<columns;j++)
    {
      m[i][j] = m[i - 1][j] - factor * m[i - 1][columns-j];
    }
#ifdef __CPROVER
      __DSVERIFIER_assert(m[i][0l] >= _poly_error);
#else
    printf("m[%d]=%f>0\n", i, m[i][0]);
    //std::cout << "m[" << i << "]=" << m[i][0] << ">0" << std::endl;
    if (!(m[i][0] >= _poly_error)) return 0;
#endif
    columns--;
  }
  return 1;
}

signed long int fxp_control_floatt_to_fxp(control_floatt value)
{
  signed long int tmp;
  control_floatt ftemp=value * _fxp_one;
  tmp = ftemp;
  control_floatt residue=ftemp - tmp;
  if(value < 0.0 && (residue != 0.0))
  {
    ftemp = ftemp - 1.0;
    tmp = ftemp;
  }
  return tmp;
}

void fxp_check(control_floatt *value)
{
#ifdef __CPROVER
  control_floatt tmp_value=*value;
  if (tmp_value < 0.0) tmp_value=-tmp_value;
  __DSVERIFIER_assert((~_dbl_max&tmp_value)==0);
#else
  *value=fxp_control_floatt_to_fxp(*value);
  *value/=_fxp_one;
#endif
}

void fxp_check_array(control_floatt *f, cnttype N)
{
  for(cnttype i=0; i < N; i++) fxp_check(&f[i]);
}

void poly_mult(control_floatt *a, cnttype Na, control_floatt *b, cnttype Nb, control_floatt *ans, cnttype Nans)
{
  cnttype i;
  cnttype j;
  cnttype k;
  Nans = Na + Nb - 1;
  for(i = 0 ; i<Nans; i++) ans[i] = 0.0;
  for(i = 0; i < Na; i++)
  {
    for( j = 0; j < Nb; j++)
    {
      k = Na + Nb -i -j -2;
      ans[k] += a[Na-i-1] * b[Nb-j-1];
    }
  }
}

void poly_sum(control_floatt *a, cnttype Na, control_floatt *b, cnttype Nb, control_floatt *ans, cnttype Nans)
{
  cnttype i;
  Nans--;
  Na--;
  Nb--;
  for (i=0;i<=Na;i++) ans[Nans-i]=a[Na-i];
  for (i=Na+1;i<=Nans;i++) ans[Nans-i]=0;
  for (i=0;i<=Nb;i++) ans[Nans-i]+=b[Nb-i];
}

void ft_closedloop_series(control_floatt *c_num, cnttype Nc_num, control_floatt *c_den, cnttype Nc_den, control_floatt *plant_num, cnttype Nplant_num, control_floatt *plant_den, cnttype Nplant_den, control_floatt *ans_num, cnttype Nans_num, control_floatt *ans_den, cnttype Nans_den)
{
  Nans_num = Nc_num + Nplant_num -1;
  Nans_den = Nc_den + Nplant_den -1;
  control_floatt den_mult[Nans_den];
  poly_mult(c_num, Nc_num, plant_num, Nplant_num, ans_num, Nans_num);
  poly_mult(c_den, Nc_den, plant_den, Nplant_den, den_mult, Nans_den);
  poly_sum(ans_num, Nans_num, den_mult, Nans_den, ans_den, Nans_den);
}

int verify_stability_closedloop_using_dslib(void)
{
  fxp_check_array(controller.num,__CONTROLLER_NUM_SIZE);
  fxp_check_array(controller.den,__CONTROLLER_DEN_SIZE);

  cnttype ans_num_size=__CONTROLLER_NUM_SIZE + plant.num_size-1;
  control_floatt ans_num[ans_num_size];
  cnttype ans_den_size=__CONTROLLER_DEN_SIZE + plant.den_size-1;
  control_floatt ans_den[ans_den_size];
#ifdef __CPROVER
  __CPROVER_array_set(ans_num,0.0);
  __CPROVER_array_set(ans_den,0.0);
#else
  for (int i=0;i<ans_num_size;i++) ans_num[i]=3;
  for (int i=0;i<ans_den_size;i++) ans_den[i]=3;
#endif
/*  signed int return_value1=check_stability_closedloop(controller.num, __CONTROLLER_NUM_SIZE);
#ifdef __CPROVER
  __DSVERIFIER_assert(!(return_value1 == 0));
#else
  if (return_value1 == 0) return 10;
#endif*/
  ft_closedloop_series(controller.num, __CONTROLLER_NUM_SIZE, controller.den, __CONTROLLER_DEN_SIZE, plant_cbmc.num, plant.num_size, plant_cbmc.den, plant.den_size, ans_num, ans_num_size, ans_den, ans_den_size);
  signed int return_value2=check_stability_closedloop(ans_den, ans_den_size);
#ifdef __CPROVER
  __DSVERIFIER_assert(!(return_value2 == 0));
#else
  fputs("plant_num=", stdout);
  //std::cout << "plant_num=";
  print_poly(plant_cbmc.num,plant_cbmc.num_size);
  fputs("plant_den=", stdout);
  //std::cout << "plant_den=";
  print_poly(plant_cbmc.den, plant_cbmc.den_size);
  fputs("ans=", stdout);
  //std::cout << "ans=";
  print_poly(ans_den, ans_den_size);
  if (return_value2 == 0) return 10;
#endif
  return 0;
}

// main
int main()
{
  initialization();
  int result=validation();
#ifndef __CPROVER
  if (result!=0) return 10;
#endif
  call_closedloop_verification_task();
#ifdef __CPROVER
  assert_nonzero_controller();
#else
  if (assert_nonzero_controller() == 0) return 10;
#endif
  result=verify_stability_closedloop_using_dslib();
#ifdef __CPROVER
  //__DSVERIFIER_assert(0);
#else
  if (result!=0) return 10;
#endif
  return 0;
}
