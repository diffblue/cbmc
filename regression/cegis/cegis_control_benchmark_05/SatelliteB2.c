// tag-#anon#ST[ARR100{F64}$F64$'a'|S32'a_size'|U32'$pad0'|ARR100{F64}$F64$'b'|S32'b_size'|U32'$pad1'|F64'sample_time'|ARR100{F64}$F64$'a_uncertainty'|ARR100{F64}$F64$'b_uncertainty']
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 144
struct anonymous$0;

// tag-#anon#ST[ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'A'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'B'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'C'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'D'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'states'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'outputs'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'inputs'|ARR20{ARR20{F64}$F64$}$ARR20{F64}$F64$$'K'|U32'nStates'|U32'nInputs'|U32'nOutputs'|U32'$pad0']
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 156
struct anonymous$1;

// tag-#anon#ST[S32'int_bits'|S32'frac_bits'|F64'max'|F64'min'|S32'default_realization'|U32'$pad0'|F64'delta'|S32'scale'|U32'$pad1'|F64'max_error']
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 171
struct anonymous$3;

// tag-#anon#ST[S32'push'|S32'in'|S32'sbiw'|S32'cli'|S32'out'|S32'std'|S32'ldd'|S32'subi'|S32'sbci'|S32'lsl'|S32'rol'|S32'add'|S32'adc'|S32'adiw'|S32'rjmp'|S32'mov'|S32'sbc'|S32'ld'|S32'rcall'|S32'cp'|S32'cpc'|S32'ldi'|S32'brge'|S32'pop'|S32'ret'|S32'st'|S32'brlt'|S32'cpi']
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 183
struct anonymous;

// tag-#anon#ST[S64'clock'|S32'device'|U32'$pad0'|F64'cycle'|SYM#tag-#anon#ST[S32'push'|S32'in'|S32'sbiw'|S32'cli'|S32'out'|S32'std'|S32'ldd'|S32'subi'|S32'sbci'|S32'lsl'|S32'rol'|S32'add'|S32'adc'|S32'adiw'|S32'rjmp'|S32'mov'|S32'sbc'|S32'ld'|S32'rcall'|S32'cp'|S32'cpc'|S32'ldi'|S32'brge'|S32'pop'|S32'ret'|S32'st'|S32'brlt'|S32'cpi']#'assembly']
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 215
struct anonymous$2;

#include <assert.h>

#ifndef IEEE_FLOAT_EQUAL
#define IEEE_FLOAT_EQUAL(x,y) ((x)==(y))
#endif
#ifndef IEEE_FLOAT_NOTEQUAL
#define IEEE_FLOAT_NOTEQUAL(x,y) ((x)!=(y))
#endif

// __DSVERIFIER_assert
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 35
void __DSVERIFIER_assert(_Bool expression);
// __DSVERIFIER_assert_msg
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 39
void __DSVERIFIER_assert_msg(_Bool expression, char *msg);
// __DSVERIFIER_assume
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 21
void __DSVERIFIER_assume(_Bool expression);
// __assert_fail
// file /usr/include/assert.h line 67
extern void __assert_fail(const char *, const char *, unsigned int, const char *) _Noreturn;
// call_closedloop_verification_task
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 369
void call_closedloop_verification_task(void *closedloop_verification_task);
// call_verification_task
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 268
void call_verification_task(void *verification_task);
// check_stability
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 59
signed int check_stability(double *a, signed int n);
// check_stability_closedloop
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 70
signed int check_stability_closedloop(double *a, signed int n, double *plant_num, signed int p_num_size, double *plant_den, signed int p_den_size);
// determinant
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 498
double determinant(double (*a)[20l], signed int n);
// double_add_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 315
void double_add_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], double (*m2)[20l], double (*result)[20l]);
// double_check_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 218
void double_check_limit_cycle(double *y, signed int y_size);
// double_check_oscillations
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 187
void double_check_oscillations(double *y, signed int y_size);
// double_check_persistent_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 254
void double_check_persistent_limit_cycle(double *y, signed int y_size);
// double_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 83
double double_direct_form_1(double *y, double *x, double *a, double *b, signed int Na, signed int Nb);
// double_direct_form_1_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 205
double double_direct_form_1_MSP430(double *y, double *x, double *a, double *b, signed int Na, signed int Nb);
// double_direct_form_1_impl2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 364
void double_direct_form_1_impl2(double *x, signed int x_size, double *b, signed int b_size, double *a, signed int a_size, double *y);
// double_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 102
double double_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// double_direct_form_2_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 230
double double_direct_form_2_MSP430(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// double_exp_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 428
void double_exp_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], unsigned int expNumber, double (*result)[20l]);
// double_matrix_multiplication
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 337
void double_matrix_multiplication(unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, double (*m1)[20l], double (*m2)[20l], double (*m3)[20l]);
// double_state_space_representation
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 23
double double_state_space_representation(void);
// double_sub_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 326
void double_sub_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], double (*m2)[20l], double (*result)[20l]);
// double_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 122
double double_transposed_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// double_transposed_direct_form_2_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 257
double double_transposed_direct_form_2_MSP430(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// exit
// file /usr/include/stdlib.h line 543
extern void exit(signed int) _Noreturn;
// fatorial
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 54
signed int fatorial(signed int n);
// float_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 144
float float_direct_form_1(float *y, float *x, float *a, float *b, signed int Na, signed int Nb);
// float_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 163
float float_direct_form_2(float *w, float x, float *a, float *b, signed int Na, signed int Nb);
// float_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 183
float float_transposed_direct_form_2(float *w, float x, float *a, float *b, signed int Na, signed int Nb);
// ft_closedloop_feedback
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 57
void ft_closedloop_feedback(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den);
// ft_closedloop_sensitivity
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 42
void ft_closedloop_sensitivity(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den);
// ft_closedloop_series
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 28
void ft_closedloop_series(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den);
// fxp_abs
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 303
signed long int fxp_abs(signed long int a);
// fxp_add
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 315
signed long int fxp_add(signed long int aadd, signed long int badd);
// fxp_add_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 467
void fxp_add_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*result)[20l]);
// fxp_check_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 163
void fxp_check_limit_cycle(signed long int *y, signed int y_size);
// fxp_check_oscillations
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 253
void fxp_check_oscillations(signed long int *y, signed int y_size);
// fxp_check_persistent_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 201
void fxp_check_persistent_limit_cycle(signed long int *y, signed int y_size);
// fxp_determinant
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 529
double fxp_determinant(signed long int (*a_fxp)[20l], signed int n);
// fxp_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 22
signed long int fxp_direct_form_1(signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed int Na, signed int Nb);
// fxp_direct_form_1_impl2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 388
void fxp_direct_form_1_impl2(signed long int *x, signed int x_size, signed long int *b, signed int b_size, signed long int *a, signed int a_size, signed long int *y);
// fxp_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 41
signed long int fxp_direct_form_2(signed long int *w, signed long int x, signed long int *a, signed long int *b, signed int Na, signed int Nb);
// fxp_div
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 357
signed long int fxp_div(signed long int a, signed long int b);
// fxp_double_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 211
signed long int fxp_double_to_fxp(double value);
// fxp_double_to_fxp_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 247
void fxp_double_to_fxp_array(double *f, signed long int *r, signed int N);
// fxp_exp_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 390
void fxp_exp_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], unsigned int expNumber, signed long int (*result)[20l]);
// fxp_float_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 198
signed long int fxp_float_to_fxp(float f);
// fxp_float_to_fxp_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 240
void fxp_float_to_fxp_array(float *f, signed long int *r, signed int N);
// fxp_get_frac_part
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 125
signed long int fxp_get_frac_part(signed long int in);
// fxp_get_int_part
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 115
signed long int fxp_get_int_part(signed long int in);
// fxp_int_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 170
signed long int fxp_int_to_fxp(signed int in);
// fxp_ln
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 288
signed int fxp_ln(signed int x);
// fxp_log10
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 345
double fxp_log10(double x);
// fxp_log10_low
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 333
double fxp_log10_low(double x);
// fxp_matrix_multiplication
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 368
void fxp_matrix_multiplication(unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*m3)[20l]);
// fxp_mult
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 339
signed long int fxp_mult(signed long int amult, signed long int bmult);
// fxp_neg
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 367
signed long int fxp_neg(signed long int aneg);
// fxp_print_float
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 407
void fxp_print_float(signed long int a);
// fxp_print_float_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 411
void fxp_print_float_array(signed long int *a, signed int N);
// fxp_print_int
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 403
void fxp_print_int(signed long int a);
// fxp_quantize
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 136
signed long int fxp_quantize(signed long int aquant);
// fxp_shrl
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 390
signed long int fxp_shrl(signed long int in, signed int shift);
// fxp_sign
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 380
signed long int fxp_sign(signed long int a);
// fxp_square
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 399
signed long int fxp_square(signed long int a);
// fxp_state_space_representation
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 67
double fxp_state_space_representation(void);
// fxp_sub
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 327
signed long int fxp_sub(signed long int asub, signed long int bsub);
// fxp_sub_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 474
void fxp_sub_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*result)[20l]);
// fxp_to_double
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 271
double fxp_to_double(signed long int fxp);
// fxp_to_double_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 291
void fxp_to_double_array(double *f, signed long int *r, signed int N);
// fxp_to_float
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 264
float fxp_to_float(signed long int fxp);
// fxp_to_float_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 284
void fxp_to_float_array(float *f, signed long int *r, signed int N);
// fxp_to_int
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 182
signed int fxp_to_int(signed long int fxp);
// fxp_transpose
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 582
void fxp_transpose(signed long int (*a)[20l], signed long int (*b)[20l], signed int n, signed int m);
// fxp_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 61
signed long int fxp_transposed_direct_form_2(signed long int *w, signed long int x, signed long int *a, signed long int *b, signed int Na, signed int Nb);
// fxp_verify_overflow
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 153
void fxp_verify_overflow(signed long int value);
// fxp_verify_overflow_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 158
void fxp_verify_overflow_array(signed long int *array, signed int n);
// generate_delta_coefficients
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 33
void generate_delta_coefficients(double *vetor, double *out, signed int n, double delta);
// generic_timing_double_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 286
double generic_timing_double_direct_form_1(double *y, double *x, double *a, double *b, signed int Na, signed int Nb);
// generic_timing_double_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 311
double generic_timing_double_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// generic_timing_double_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 338
double generic_timing_double_transposed_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// generic_timing_shift_l_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 20
double generic_timing_shift_l_double(double zIn, double *z, signed int N);
// generic_timing_shift_r_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 37
double generic_timing_shift_r_double(double zIn, double *z, signed int N);
// get_delta_transfer_function
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 52
void get_delta_transfer_function(double *b, double *b_out, signed int b_size, double *a, double *a_out, signed int a_size, double delta);
// get_delta_transfer_function_with_base
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 59
void get_delta_transfer_function_with_base(double *b, double *b_out, signed int b_size, double *a, double *a_out, signed int a_size, double delta);
// iirIIOutTime
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 428
float iirIIOutTime(float *w, float x, float *a, float *b, signed int Na, signed int Nb);
// iirIItOutTime
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 452
float iirIItOutTime(float *w, float x, float *a, float *b, signed int Na, signed int Nb);
// iirIItOutTime_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 479
double iirIItOutTime_double(double *w, double x, double *a, double *b, signed int Na, signed int Nb);
// iirOutBoth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 506
void iirOutBoth(float *yf, float *xf, float *af, float *bf, float *sumf_ref, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int *sum_ref, signed int Na, signed int Nb);
// iirOutBothL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 586
float iirOutBothL(float *yf, float *xf, float *af, float *bf, float xfin, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int xin, signed int Na, signed int Nb);
// iirOutBothL2
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 626
float iirOutBothL2(float *yf, float *xf, float *af, float *bf, float xfin, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int xin, signed int Na, signed int Nb);
// iirOutFixedL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 536
signed long int iirOutFixedL(signed long int *y, signed long int *x, signed long int xin, signed long int *a, signed long int *b, signed int Na, signed int Nb);
// iirOutFloatL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 561
float iirOutFloatL(float *y, float *x, float xin, float *a, float *b, signed int Na, signed int Nb);
// initialization
// file /home/lucascordeiro/dsverifier/bmc/core/initialization.h line 24
void initialization();
// initialize_array
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 22
void initialize_array(double *v, signed int n);
// initials
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 52
extern void initials();
// internal_abs
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 49
double internal_abs(double a);
// internal_pow
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 39
double internal_pow(double a, double b);
// nchoosek
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 23
signed int nchoosek(signed int n, signed int k);
// nondet_double
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle_closedloop.h line 27
double nondet_double();
// nondet_float
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_overflow.h line 18
float nondet_float();
// nondet_int
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_overflow.h line 17
signed int nondet_int();
// order
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 158
signed int order(signed int Na, signed int Nb);
// poly_mult
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 165
void poly_mult(double *a, signed int Na, double *b, signed int Nb, double *ans, signed int Nans);
// poly_sum
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 141
void poly_sum(double *a, signed int Na, double *b, signed int Nb, double *ans, signed int Nans);
// print_array_elements
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 305
void print_array_elements(char *name, double *v, signed int n);
// print_fxp_array_elements
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 419
void print_fxp_array_elements(char *name, signed long int *v, signed int n);
// print_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 481
void print_matrix(double (*matrix)[20l], unsigned int lines, unsigned int columns);
// printf
// file /usr/include/stdio.h line 362
extern signed int printf(const char *, ...);
// rand
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 417
extern signed int rand(void);
// revert_array
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 30
void revert_array(double *v, double *out, signed int n);
// shiftL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 53
signed long int shiftL(signed long int zIn, signed long int *z, signed int N);
// shiftLDouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 119
double shiftLDouble(double zIn, double *z, signed int N);
// shiftLboth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 130
void shiftLboth(float zfIn, float *zf, signed long int zIn, signed long int *z, signed int N);
// shiftLfloat
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 75
float shiftLfloat(float zIn, float *z, signed int N);
// shiftR
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 64
signed long int shiftR(signed long int zIn, signed long int *z, signed int N);
// shiftRDdouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 97
double shiftRDdouble(double zIn, double *z, signed int N);
// shiftRboth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 144
void shiftRboth(float zfIn, float *zf, signed long int zIn, signed long int *z, signed int N);
// shiftRdouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 108
double shiftRdouble(double zIn, double *z, signed int N);
// shiftRfloat
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 86
float shiftRfloat(float zIn, float *z, signed int N);
// snrPoint
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 402
float snrPoint(float *s, float *n, signed int blksz);
// snrPower
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 381
float snrPower(float *s, float *n, signed int blksz);
// snrVariance
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 357
float snrVariance(float *s, float *n, signed int blksz);
// srand
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 423
extern void srand(unsigned int seed);
// transpose
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 571
void transpose(double (*a)[20l], double (*b)[20l], signed int n, signed int m);
// validation
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 125
void validation();
// verify_controllability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_controllability.h line 16
signed int verify_controllability(void);
// verify_controllability_double
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_controllability.h line 120
signed int verify_controllability_double(void);
// verify_error
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error.h line 20
signed int verify_error(void);
// verify_error_closedloop
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error_closedloop.h line 27
signed int verify_error_closedloop(void);
// verify_error_state_space
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error_state_space.h line 20
signed int verify_error_state_space(void);
// verify_generic_timing
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_generic_timing.h line 25
signed int verify_generic_timing(void);
// verify_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle.h line 111
signed int verify_limit_cycle(void);
// verify_limit_cycle_closed_loop
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle_closedloop.h line 29
signed int verify_limit_cycle_closed_loop(void);
// verify_limit_cycle_state_space
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle.h line 21
signed int verify_limit_cycle_state_space(void);
// verify_minimum_phase
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_minimum_phase.h line 24
signed int verify_minimum_phase(void);
// verify_observability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_observability.h line 19
signed int verify_observability(void);
// verify_overflow
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_overflow.h line 23
signed int verify_overflow(void);
// verify_stability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_stability.h line 24
signed int verify_stability(void);
// verify_stability_closedloop_using_dslib
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_stability_closedloop.h line 21
signed int verify_stability_closedloop_using_dslib(void);
// verify_timing_msp_430
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_timing_msp430.h line 22
signed int verify_timing_msp_430(void);
// verify_zero_input_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_zero_input_limit_cycle.h line 16
signed int verify_zero_input_limit_cycle(void);
// wrap
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 100
signed long int wrap(signed long int kX, signed long int kLowerBound, signed long int kUpperBound);

struct anonymous$0
{
  // a
  double a[100l];
  // a_size
  signed int a_size;
  // b
  double b[100l];
  // b_size
  signed int b_size;
  // sample_time
  double sample_time;
  // a_uncertainty
  double a_uncertainty[100l];
  // b_uncertainty
  double b_uncertainty[100l];
};

struct anonymous$1
{
  // A
  double A[20l][20l];
  // B
  double B[20l][20l];
  // C
  double C[20l][20l];
  // D
  double D[20l][20l];
  // states
  double states[20l][20l];
  // outputs
  double outputs[20l][20l];
  // inputs
  double inputs[20l][20l];
  // K
  double K[20l][20l];
  // nStates
  unsigned int nStates;
  // nInputs
  unsigned int nInputs;
  // nOutputs
  unsigned int nOutputs;
};

struct anonymous$3
{
  // int_bits
  signed int int_bits;
  // frac_bits
  signed int frac_bits;
  // max
  double max;
  // min
  double min;
  // default_realization
  signed int default_realization;
  // delta
  double delta;
  // scale
  signed int scale;
  // max_error
  double max_error;
};

struct anonymous
{
  // push
  signed int push;
  // in
  signed int in;
  // sbiw
  signed int sbiw;
  // cli
  signed int cli;
  // out
  signed int out;
  // std
  signed int std;
  // ldd
  signed int ldd;
  // subi
  signed int subi;
  // sbci
  signed int sbci;
  // lsl
  signed int lsl;
  // rol
  signed int rol;
  // add
  signed int add;
  // adc
  signed int adc;
  // adiw
  signed int adiw;
  // rjmp
  signed int rjmp;
  // mov
  signed int mov;
  // sbc
  signed int sbc;
  // ld
  signed int ld;
  // rcall
  signed int rcall;
  // cp
  signed int cp;
  // cpc
  signed int cpc;
  // ldi
  signed int ldi;
  // brge
  signed int brge;
  // pop
  signed int pop;
  // ret
  signed int ret;
  // st
  signed int st;
  // brlt
  signed int brlt;
  // cpi
  signed int cpi;
};

struct anonymous$2
{
  // clock
  signed long int clock;
  // device
  signed int device;
  // cycle
  double cycle;
  // assembly
  struct anonymous assembly;
};


// X_SIZE_VALUE
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 121
signed int X_SIZE_VALUE=0;
// _controller
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 17
extern struct anonymous$1 _controller;
// _dbl_max
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 45
double _dbl_max;
// _dbl_min
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 46
double _dbl_min;
// _fxp_fmask
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 49
signed long int _fxp_fmask;
// _fxp_half
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 39
signed long int _fxp_half;
// _fxp_imask
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 52
signed long int _fxp_imask;
// _fxp_max
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 42
signed long int _fxp_max;
// _fxp_min
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 41
signed long int _fxp_min;
// _fxp_minus_one
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 40
signed long int _fxp_minus_one;
// _fxp_one
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 38
signed long int _fxp_one;
// controller
// file input.c line 3
struct anonymous$0 controller={ .a={ 1.000000, (double)-4.200000e-1f, (double)-3.465000e-1f, (double)-3.915000e-2f, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .a_size=4,
    .b={ 2.880000e+0, (double)-4.896000e+0f, 2.074000e+0, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .b_size=3,
    .sample_time=1.000000, .a_uncertainty={ 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .b_uncertainty={ 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 } };
// ds
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 17
extern struct anonymous$0 ds;
// error_limit
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error_state_space.h line 18
extern double error_limit;
// generic_timer
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_generic_timing.h line 23
signed int generic_timer=0;
// hw
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 18
extern struct anonymous$2 hw;
// impl
// file input.c line 11
struct anonymous$3 impl={ .int_bits=3, .frac_bits=7, .max=1.000000, .min=-1.000000,
    .default_realization=0, .delta=0.000000,
    .scale=1, .max_error=0.000000 };
// nInputs
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 20
extern signed int nInputs;
// nOutputs
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 21
extern signed int nOutputs;
// nStates
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 19
extern signed int nStates;
// next
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 416
unsigned long int next=1ul;
// overflow_mode
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 122
signed int overflow_mode=1;
// plant
// file input.c line 19
struct anonymous$0 plant={ .a={ 1.000000, (double)-2.000000f, 1.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .a_size=3,
    .b={ 1.250000e-1, 1.250000e-1, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .b_size=2,
    .sample_time=0.000000, .a_uncertainty={ 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 }, .b_uncertainty={ 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000, 0.000000 } };
// plant_cbmc
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 46
struct anonymous$0 plant_cbmc;
// rounding_mode
// file /home/lucascordeiro/dsverifier/bmc/core/definitions.h line 123
signed int rounding_mode=0;
// scale_factor
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 55
static const double scale_factor[31l]={ 1.000000, 2.000000, 4.000000, 8.000000, 16.000000, 32.000000, 64.000000, 128.000000, 256.000000, 512.000000, 1024.000000, 2048.000000, 4096.000000, 8192.000000, 16384.000000, 32768.000000, 65536.000000, 1.310720e+5, 2.621440e+5, 5.242880e+5, 1.048576e+6, 2.097152e+6, 4.194304e+6, 8.388608e+6, 1.677722e+7, 3.355443e+7, 6.710886e+7, 1.342177e+8, 2.684355e+8, 5.368709e+8, 1.073742e+9 };
// scale_factor_inv
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 62
static const double scale_factor_inv[31l]={ 1.000000, 5.000000e-1, 2.500000e-1, 1.250000e-1, 6.250000e-2, 3.125000e-2, 1.562500e-2, 7.812500e-3, 3.906250e-3, 1.953125e-3, 9.765625e-4, 4.882813e-4, 2.441406e-4, 1.220703e-4, 6.103516e-5, 3.051758e-5, 1.525879e-5, 7.629395e-6, 3.814697e-6, 1.907349e-6, 9.536743e-7, 4.768372e-7, 2.384186e-7, 1.192093e-7, 5.960465e-8, 2.980232e-8, 1.490116e-8, 7.450581e-9, 3.725290e-9, 1.862645e-9, 9.313230e-10 };

// __DSVERIFIER_assert
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 35
void __DSVERIFIER_assert(_Bool expression)
{
  /* assertion expression */
  assert(expression != (_Bool)0);
  if(!(expression == (_Bool)0))
    (void)0;

}

// __DSVERIFIER_assert_msg
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 39
void __DSVERIFIER_assert_msg(_Bool expression, char *msg)
{
  printf("%c", msg);
  /* assertion expression */
  assert(expression != (_Bool)0);
  if(!(expression == (_Bool)0))
    (void)0;

}

// __DSVERIFIER_assume
// file /home/lucascordeiro/dsverifier/bmc/core/compatibility.h line 21
void __DSVERIFIER_assume(_Bool expression)
{
  __CPROVER_assume(expression != (_Bool)0);
}

// call_closedloop_verification_task
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 369
void call_closedloop_verification_task(void *closedloop_verification_task)
{
  _Bool base_case_executed=(_Bool)0;
  signed int i=0;
  i = 0;
  for( ; !(i >= plant.b_size); i = i + 1)
  {
    if(plant.b_uncertainty[(signed long int)i] > 0.000000)
    {
      double call_closedloop_verification_task$$1$$1$$1$$1$$factor=(plant.b[(signed long int)i] * plant.b_uncertainty[(signed long int)i]) / 100.000000;
      call_closedloop_verification_task$$1$$1$$1$$1$$factor = call_closedloop_verification_task$$1$$1$$1$$1$$factor < 0.000000 ? call_closedloop_verification_task$$1$$1$$1$$1$$factor * (double)-1 : call_closedloop_verification_task$$1$$1$$1$$1$$factor;
      double call_closedloop_verification_task$$1$$1$$1$$1$$min=plant.b[(signed long int)i] - call_closedloop_verification_task$$1$$1$$1$$1$$factor;
      double call_closedloop_verification_task$$1$$1$$1$$1$$max=plant.b[(signed long int)i] + call_closedloop_verification_task$$1$$1$$1$$1$$factor;
      if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(call_closedloop_verification_task$$1$$1$$1$$1$$factor, 0.000000))
        goto __CPROVER_DUMP_L9;

      else
        if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(call_closedloop_verification_task$$1$$1$$1$$1$$factor, 0.000000))
          base_case_executed = (_Bool)0;

      plant_cbmc.b[(signed long int)i] = nondet_double();
      _Bool tmp_if_expr$1;
      if(plant_cbmc.b[(signed long int)i] >= call_closedloop_verification_task$$1$$1$$1$$1$$min)
        tmp_if_expr$1 = plant_cbmc.b[(signed long int)i] <= call_closedloop_verification_task$$1$$1$$1$$1$$max ? (_Bool)1 : (_Bool)0;

      else
        tmp_if_expr$1 = (_Bool)0;
      __DSVERIFIER_assume(tmp_if_expr$1);
    }

    else
      plant_cbmc.b[(signed long int)i] = plant.b[(signed long int)i];

  __CPROVER_DUMP_L9:
    ;
  }
  i = 0;
  for( ; !(i >= plant.a_size); i = i + 1)
  {
    if(plant.a_uncertainty[(signed long int)i] > 0.000000)
    {
      double factor=(plant.a[(signed long int)i] * plant.a_uncertainty[(signed long int)i]) / 100.000000;
      factor = factor < 0.000000 ? factor * (double)-1 : factor;
      double min=plant.a[(signed long int)i] - factor;
      double max=plant.a[(signed long int)i] + factor;
      if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(factor, 0.000000))
        goto __CPROVER_DUMP_L19;

      else
        if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(factor, 0.000000))
          base_case_executed = (_Bool)0;

      plant_cbmc.a[(signed long int)i] = nondet_double();
      _Bool tmp_if_expr$2;
      if(plant_cbmc.a[(signed long int)i] >= min)
        tmp_if_expr$2 = plant_cbmc.a[(signed long int)i] <= max ? (_Bool)1 : (_Bool)0;

      else
        tmp_if_expr$2 = (_Bool)0;
      __DSVERIFIER_assume(tmp_if_expr$2);
    }

    else
      plant_cbmc.a[(signed long int)i] = plant.a[(signed long int)i];

  __CPROVER_DUMP_L19:
    ;
  }
  ((void (*)())closedloop_verification_task)();
}

// call_verification_task
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 268
void call_verification_task(void *verification_task)
{
  signed int i=0;
  _Bool base_case_executed=(_Bool)0;
  if((_Bool)0)
  {
    i = 0;
    for( ; !(i >= ds.b_size); i = i + 1)
    {
      if(ds.b_uncertainty[(signed long int)i] > 0.000000)
      {
        double call_verification_task$$1$$1$$1$$1$$1$$factor=ds.b_uncertainty[(signed long int)i];
        call_verification_task$$1$$1$$1$$1$$1$$factor = call_verification_task$$1$$1$$1$$1$$1$$factor < 0.000000 ? call_verification_task$$1$$1$$1$$1$$1$$factor * (double)-1 : call_verification_task$$1$$1$$1$$1$$1$$factor;
        double min=ds.b[(signed long int)i] - call_verification_task$$1$$1$$1$$1$$1$$factor;
        double max=ds.b[(signed long int)i] + call_verification_task$$1$$1$$1$$1$$1$$factor;
        if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$1$$1$$1$$1$$factor, 0.000000))
          goto __CPROVER_DUMP_L8;

        else
          if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$1$$1$$1$$1$$factor, 0.000000))
            base_case_executed = (_Bool)0;

        ds.b[(signed long int)i] = nondet_double();
        _Bool tmp_if_expr$1;
        if(ds.b[(signed long int)i] >= min)
          tmp_if_expr$1 = ds.b[(signed long int)i] <= max ? (_Bool)1 : (_Bool)0;

        else
          tmp_if_expr$1 = (_Bool)0;
        __DSVERIFIER_assume(tmp_if_expr$1);
      }


    __CPROVER_DUMP_L8:
      ;
    }
    i = 0;
    for( ; !(i >= ds.a_size); i = i + 1)
    {
      if(ds.a_uncertainty[(signed long int)i] > 0.000000)
      {
        double factor=ds.a_uncertainty[(signed long int)i];
        factor = factor < 0.000000 ? factor * (double)-1 : factor;
        double call_verification_task$$1$$1$$2$$1$$1$$min=ds.a[(signed long int)i] - factor;
        double call_verification_task$$1$$1$$2$$1$$1$$max=ds.a[(signed long int)i] + factor;
        if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(factor, 0.000000))
          goto __CPROVER_DUMP_L17;

        else
          if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(factor, 0.000000))
            base_case_executed = (_Bool)0;

        ds.a[(signed long int)i] = nondet_double();
        _Bool tmp_if_expr$2;
        if(ds.a[(signed long int)i] >= call_verification_task$$1$$1$$2$$1$$1$$min)
          tmp_if_expr$2 = ds.a[(signed long int)i] <= call_verification_task$$1$$1$$2$$1$$1$$max ? (_Bool)1 : (_Bool)0;

        else
          tmp_if_expr$2 = (_Bool)0;
        __DSVERIFIER_assume(tmp_if_expr$2);
      }


    __CPROVER_DUMP_L17:
      ;
    }
  }

  else
  {
    signed int call_verification_task$$1$$2$$i=0;
    call_verification_task$$1$$2$$i = 0;
    for( ; !(call_verification_task$$1$$2$$i >= ds.b_size); call_verification_task$$1$$2$$i = call_verification_task$$1$$2$$i + 1)
    {
      if(ds.b_uncertainty[(signed long int)call_verification_task$$1$$2$$i] > 0.000000)
      {
        double call_verification_task$$1$$2$$1$$1$$1$$factor=(ds.b[(signed long int)call_verification_task$$1$$2$$i] * ds.b_uncertainty[(signed long int)call_verification_task$$1$$2$$i]) / 100.000000;
        call_verification_task$$1$$2$$1$$1$$1$$factor = call_verification_task$$1$$2$$1$$1$$1$$factor < 0.000000 ? call_verification_task$$1$$2$$1$$1$$1$$factor * (double)-1 : call_verification_task$$1$$2$$1$$1$$1$$factor;
        double call_verification_task$$1$$2$$1$$1$$1$$min=ds.b[(signed long int)call_verification_task$$1$$2$$i] - call_verification_task$$1$$2$$1$$1$$1$$factor;
        double call_verification_task$$1$$2$$1$$1$$1$$max=ds.b[(signed long int)call_verification_task$$1$$2$$i] + call_verification_task$$1$$2$$1$$1$$1$$factor;
        if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$2$$1$$1$$1$$factor, 0.000000))
          goto __CPROVER_DUMP_L27;

        else
          if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$2$$1$$1$$1$$factor, 0.000000))
            base_case_executed = (_Bool)0;

        ds.b[(signed long int)call_verification_task$$1$$2$$i] = nondet_double();
        _Bool tmp_if_expr$3;
        if(ds.b[(signed long int)call_verification_task$$1$$2$$i] >= call_verification_task$$1$$2$$1$$1$$1$$min)
          tmp_if_expr$3 = ds.b[(signed long int)call_verification_task$$1$$2$$i] <= call_verification_task$$1$$2$$1$$1$$1$$max ? (_Bool)1 : (_Bool)0;

        else
          tmp_if_expr$3 = (_Bool)0;
        __DSVERIFIER_assume(tmp_if_expr$3);
      }


    __CPROVER_DUMP_L27:
      ;
    }
    call_verification_task$$1$$2$$i = 0;
    for( ; !(call_verification_task$$1$$2$$i >= ds.a_size); call_verification_task$$1$$2$$i = call_verification_task$$1$$2$$i + 1)
    {
      if(ds.a_uncertainty[(signed long int)call_verification_task$$1$$2$$i] > 0.000000)
      {
        double call_verification_task$$1$$2$$2$$1$$1$$factor=(ds.a[(signed long int)call_verification_task$$1$$2$$i] * ds.a_uncertainty[(signed long int)call_verification_task$$1$$2$$i]) / 100.000000;
        call_verification_task$$1$$2$$2$$1$$1$$factor = call_verification_task$$1$$2$$2$$1$$1$$factor < 0.000000 ? call_verification_task$$1$$2$$2$$1$$1$$factor * (double)-1 : call_verification_task$$1$$2$$2$$1$$1$$factor;
        double call_verification_task$$1$$2$$2$$1$$1$$min=ds.a[(signed long int)call_verification_task$$1$$2$$i] - call_verification_task$$1$$2$$2$$1$$1$$factor;
        double call_verification_task$$1$$2$$2$$1$$1$$max=ds.a[(signed long int)call_verification_task$$1$$2$$i] + call_verification_task$$1$$2$$2$$1$$1$$factor;
        if((signed int)base_case_executed == 1 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$2$$2$$1$$1$$factor, 0.000000))
          goto __CPROVER_DUMP_L36;

        else
          if((signed int)base_case_executed == 0 && IEEE_FLOAT_EQUAL(call_verification_task$$1$$2$$2$$1$$1$$factor, 0.000000))
            base_case_executed = (_Bool)0;

        ds.a[(signed long int)call_verification_task$$1$$2$$i] = nondet_double();
        _Bool tmp_if_expr$4;
        if(ds.a[(signed long int)call_verification_task$$1$$2$$i] >= call_verification_task$$1$$2$$2$$1$$1$$min)
          tmp_if_expr$4 = ds.a[(signed long int)call_verification_task$$1$$2$$i] <= call_verification_task$$1$$2$$2$$1$$1$$max ? (_Bool)1 : (_Bool)0;

        else
          tmp_if_expr$4 = (_Bool)0;
        __DSVERIFIER_assume(tmp_if_expr$4);
      }


    __CPROVER_DUMP_L36:
      ;
    }
  }
  ((void (*)())verification_task)();
}

// check_stability
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 59
signed int check_stability(double *a, signed int n)
{
  signed int lines=2 * n - 1;
  signed int columns=n;
  const signed long int columns$array_size0=(signed long int)n;
  const signed long int columns$array_size1=(signed long int)lines;
  double m[columns$array_size1][columns$array_size0];
  signed int i;
  signed int j;
  const signed long int j$array_size0=(signed long int)n;
  double current_stability[j$array_size0];
  i = 0;
  for( ; !(i >= n); i = i + 1)
    current_stability[(signed long int)i] = a[(signed long int)i];
  double sum=0.000000;
  i = 0;
  for( ; !(i >= n); i = i + 1)
    sum = sum + a[(signed long int)i];
  if(sum <= 0.000000)
  {
    printf("[DEBUG] the first constraint of Jury criteria failed: (F(1) > 0)");
    return 0;
  }

  else
  {
    sum = 0.000000;
    i = 0;
    for( ; !(i >= n); i = i + 1)
    {
      double return_value_internal_pow$1=internal_pow((double)-1, (double)((n - 1) - i));
      sum = sum + a[(signed long int)i] * return_value_internal_pow$1;
    }
    double return_value_internal_pow$2=internal_pow((double)-1, (double)(n - 1));
    sum = sum * return_value_internal_pow$2;
    if(sum <= 0.000000)
    {
      printf("[DEBUG] the second constraint of Jury criteria failed: (F(-1)*(-1)^n > 0)");
      return 0;
    }

    else
    {
      double return_value_internal_abs$3=internal_abs(a[(signed long int)(n - 1)]);
      if(return_value_internal_abs$3 > *a)
      {
        printf("[DEBUG] the third constraint of Jury criteria failed: (abs(a0) < a_{n}*z^{n})");
        return 0;
      }

      else
      {
        i = 0;
        for( ; !(i >= lines); i = i + 1)
        {
          j = 0;
          for( ; !(j >= columns); j = j + 1)
            m[(signed long int)i][(signed long int)j] = 0.000000;
        }
        i = 0;
        for( ; !(i >= lines); i = i + 1)
        {
          j = 0;
          for( ; !(j >= columns); j = j + 1)
            if(i == 0)
              m[(signed long int)i][(signed long int)j] = a[(signed long int)j];

            else
              if(!(i % 2 == 0))
              {
                signed int x=0;
                for( ; !(x >= columns); x = x + 1)
                  m[(signed long int)i][(signed long int)x] = m[(signed long int)(i - 1)][(signed long int)((columns - x) - 1)];
                columns = columns - 1;
                j = columns;
              }

              else
                m[(signed long int)i][(signed long int)j] = m[(signed long int)(i - 2)][(signed long int)j] - (m[(signed long int)(i - 2)][(signed long int)columns] / m[(signed long int)(i - 2)][0l]) * m[(signed long int)(i - 1)][(signed long int)j];
        }
        signed int first_is_positive=m[0l][0l] >= 0.000000 ? 1 : 0;
        i = 0;
        for( ; !(i >= lines); i = i + 1)
          if(i % 2 == 0)
          {
            signed int line_is_positive=m[(signed long int)i][0l] >= 0.000000 ? 1 : 0;
            if(!(first_is_positive == line_is_positive))
              return 0;

          }

        return 1;
      }
    }
  }
}

// check_stability_closedloop
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 70
signed int check_stability_closedloop(double *a, signed int n, double *plant_num, signed int p_num_size, double *plant_den, signed int p_den_size)
{
  signed int columns=n;
  const signed long int columns$array_size0=(signed long int)n;
  const signed long int columns$array_size1=(signed long int)(2 * n - 1);
  double m[columns$array_size1][columns$array_size0];
  signed int i;
  signed int j;
  signed int first_is_positive=0;
  double *p_num=plant_num;
  double *p_den=plant_den;
  double sum=0.000000;
  i = 0;
  for( ; !(i >= n); i = i + 1)
    sum = sum + a[(signed long int)i];
  __DSVERIFIER_assert(sum > 0.000000);
  sum = 0.000000;
  i = 0;
  for( ; !(i >= n); i = i + 1)
  {
    double return_value_internal_pow$1=internal_pow((double)-1, (double)((n - 1) - i));
    sum = sum + a[(signed long int)i] * return_value_internal_pow$1;
  }
  double return_value_internal_pow$2=internal_pow((double)-1, (double)(n - 1));
  sum = sum * return_value_internal_pow$2;
  __DSVERIFIER_assert(sum > 0.000000);
  double return_value_internal_abs$3=internal_abs(a[(signed long int)(n - 1)]);
  __DSVERIFIER_assert(return_value_internal_abs$3 < a[0l]);
  i = 0;
  for( ; !(i >= 2 * n + -1); i = i + 1)
  {
    j = 0;
    for( ; !(j >= columns); j = j + 1)
    {
      m[(signed long int)i][(signed long int)j] = 0.000000;
      if(i == 0)
        m[(signed long int)i][(signed long int)j] = a[(signed long int)j];

      else
        if(!(i % 2 == 0))
        {
          signed int x=0;
          for( ; !(x >= columns); x = x + 1)
            m[(signed long int)i][(signed long int)x] = m[(signed long int)(i - 1)][(signed long int)((columns - x) - 1)];
          columns = columns - 1;
          j = columns;
        }

        else
        {
          m[(signed long int)i][(signed long int)j] = m[(signed long int)(i - 2)][(signed long int)j] - (m[(signed long int)(i - 2)][(signed long int)columns] / m[(signed long int)(i - 2)][0l]) * m[(signed long int)(i - 1)][(signed long int)j];
          _Bool tmp_if_expr$4;
          if(m[0l][0l] >= 0.000000)
            tmp_if_expr$4 = m[(signed long int)i][0l] >= 0.000000 ? (_Bool)1 : (_Bool)0;

          else
            tmp_if_expr$4 = (_Bool)0;
          __DSVERIFIER_assert(tmp_if_expr$4);
        }
    }
  }
  return 1;
}

// determinant
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 498
double determinant(double (*a)[20l], signed int n)
{
  signed int i;
  signed int j;
  signed int j1;
  signed int j2;
  double det=0.000000;
  double m[20l][20l];
  if(n >= 1)
  {
    if(n == 1)
      det = a[0l][0l];

    else
      if(n == 2)
        det = a[0l][0l] * a[1l][1l] - a[1l][0l] * a[0l][1l];

      else
      {
        det = 0.000000;
        j1 = 0;
        for( ; !(j1 >= n); j1 = j1 + 1)
        {
          i = 0;
          for( ; !(i >= -1 + n); i = i + 1)
          {
            i = 1;
            for( ; !(i >= n); i = i + 1)
            {
              j2 = 0;
              j = 0;
              for( ; !(j >= n); j = j + 1)
                if(!(j == j1))
                {
                  m[(signed long int)(i - 1)][(signed long int)j2] = a[(signed long int)i][(signed long int)j];
                  j2 = j2 + 1;
                }

            }
          }
          double return_value_internal_pow$1=internal_pow(-1.000000, 1.000000 + (double)j1 + 1.000000);
          double return_value_determinant$2=determinant(m, n - 1);
          det = det + return_value_internal_pow$1 * a[0l][(signed long int)j1] * return_value_determinant$2;
        }
      }
  }

  return det;
}

// double_add_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 315
void double_add_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], double (*m2)[20l], double (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  i = 0u;
  for( ; !(i >= lines); i = i + 1u)
  {
    j = 0u;
    for( ; !(j >= columns); j = j + 1u)
      result[(signed long int)i][(signed long int)j] = m1[(signed long int)i][(signed long int)j] + m2[(signed long int)i][(signed long int)j];
  }
}

// double_check_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 218
void double_check_limit_cycle(double *y, signed int y_size)
{
  double reference=y[(signed long int)(y_size - 1)];
  signed int idx=0;
  signed int window_size=1;
  idx = y_size - 2;
  for( ; idx >= 0; idx = idx - 1)
    if(IEEE_FLOAT_NOTEQUAL(y[(signed long int)idx], reference))
      window_size = window_size + 1;

    else
      break;
  __DSVERIFIER_assume(window_size != y_size && window_size != 1);
  printf("window_size %d\n", window_size);
  signed int desired_elements=2 * window_size;
  signed int found_elements=0;
  idx = y_size - 1;
  for( ; idx >= 0; idx = idx - 1)
    if(!(-1 + y_size + -window_size >= idx))
    {
      printf("%.0f == %.0f\n", y[(signed long int)idx], y[(signed long int)(idx - window_size)]);
      signed int cmp_idx=idx - window_size;
      _Bool tmp_if_expr$1;
      if(cmp_idx >= 1)
        tmp_if_expr$1 = IEEE_FLOAT_EQUAL(y[(signed long int)idx], y[(signed long int)(idx - window_size)]) ? (_Bool)1 : (_Bool)0;

      else
        tmp_if_expr$1 = (_Bool)0;
      if(tmp_if_expr$1)
        found_elements = found_elements + 2;

      else
        break;
    }

  printf("desired_elements %d\n", desired_elements);
  printf("found_elements %d\n", found_elements);
  __DSVERIFIER_assert(desired_elements != found_elements);
}

// double_check_oscillations
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 187
void double_check_oscillations(double *y, signed int y_size)
{
  __DSVERIFIER_assume(IEEE_FLOAT_NOTEQUAL(y[0l], y[(signed long int)(y_size - 1)]));
  signed int window_timer=0;
  signed int window_count=0;
  signed int i;
  signed int j;
  i = 2;
  for( ; !(i >= y_size); i = i + 1)
  {
    signed int window_size=i;
    j = 0;
    for( ; !(j >= y_size); j = j + 1)
    {
      if(!(window_size >= window_timer))
      {
        window_timer = 0;
        window_count = 0;
      }

      signed int window_index=j + window_size;
      if(!(window_index >= y_size))
      {
        if(IEEE_FLOAT_EQUAL(y[(signed long int)j], y[(signed long int)window_index]))
        {
          window_count = window_count + 1;
          /* assertion !(window_count == window_size) */
          assert(!(window_count == window_size));
          if(!(window_count == window_size))
            (void)0;

        }

      }

      else
        break;
      window_timer = window_timer + 1;
    }
  }
}

// double_check_persistent_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 254
void double_check_persistent_limit_cycle(double *y, signed int y_size)
{
  signed int idy=0;
  signed int count_same=0;
  signed int window_size=0;
  double reference=y[0l];
  idy = 0;
  for( ; !(idy >= y_size); idy = idy + 1)
    if(IEEE_FLOAT_NOTEQUAL(y[(signed long int)idy], reference))
      window_size = window_size + 1;

    else
      if(!(window_size == 0))
        break;

      else
        count_same = count_same + 1;
  window_size = window_size + count_same;
  __DSVERIFIER_assume(window_size > 1 && window_size <= y_size / 2);
  const signed long int reference$array_size0=(signed long int)window_size;
  double lco_elements[reference$array_size0];
  idy = 0;
  for( ; !(idy >= y_size); idy = idy + 1)
    if(!(idy >= window_size))
      lco_elements[(signed long int)idy] = y[(signed long int)idy];

  idy = 0;
  signed int lco_idy=0;
  _Bool is_persistent=(_Bool)0;
  while(!(idy >= y_size))
  {
    signed int tmp_post$1=idy;
    idy = idy + 1;
    signed int tmp_post$2=lco_idy;
    lco_idy = lco_idy + 1;
    if(IEEE_FLOAT_EQUAL(y[(signed long int)tmp_post$1], lco_elements[(signed long int)tmp_post$2]))
      is_persistent = (_Bool)0;

    else
    {
      is_persistent = (_Bool)0;
      break;
    }
    if(lco_idy == window_size)
      lco_idy = 0;

  }
  __DSVERIFIER_assert((signed int)is_persistent == 0);
}

// double_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 83
double double_direct_form_1(double *y, double *x, double *a, double *b, signed int Na, signed int Nb)
{
  double *a_ptr;
  double *y_ptr;
  double *b_ptr;
  double *x_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    double *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    sum = sum + *tmp_post$1 * *tmp_post$2;
  }
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    double *tmp_post$3=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$4=y_ptr;
    y_ptr = y_ptr - 1l;
    sum = sum - *tmp_post$3 * *tmp_post$4;
  }
  sum = sum / a[0l];
  return sum;
}

// double_direct_form_1_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 205
double double_direct_form_1_MSP430(double *y, double *x, double *a, double *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  double *a_ptr;
  double *y_ptr;
  double *b_ptr;
  double *x_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  signed int i;
  signed int j;
  timer1 = timer1 + 91;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    double *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    sum = sum + *tmp_post$1 * *tmp_post$2;
    timer1 = timer1 + 47;
  }
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    double *tmp_post$3=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$4=y_ptr;
    y_ptr = y_ptr - 1l;
    sum = sum - *tmp_post$3 * *tmp_post$4;
    timer1 = timer1 + 57;
  }
  timer1 = timer1 + 3;
  /* assertion (double) timer1 * hw.cycle <= ds.sample_time */
  assert((double)timer1 * hw.cycle <= ds.sample_time);
  if((double)timer1 * hw.cycle <= ds.sample_time)
    (void)0;

  return sum;
}

// double_direct_form_1_impl2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 364
void double_direct_form_1_impl2(double *x, signed int x_size, double *b, signed int b_size, double *a, signed int a_size, double *y)
{
  signed int i=0;
  signed int j=0;
  const signed long int j$array_size0=(signed long int)x_size;
  double v[j$array_size0];
  i = 0;
  for( ; !(i >= x_size); i = i + 1)
  {
    v[(signed long int)i] = 0.000000;
    j = 0;
    for( ; !(j >= b_size); j = j + 1)
    {
      if(!(i >= j))
        break;

      v[(signed long int)i] = v[(signed long int)i] + x[(signed long int)(i - j)] * b[(signed long int)j];
    }
  }
  y[0l] = v[0l];
  i = 1;
  for( ; !(i >= x_size); i = i + 1)
  {
    y[(signed long int)i] = 0.000000;
    y[(signed long int)i] = y[(signed long int)i] + v[(signed long int)i];
    j = 1;
    for( ; !(j >= a_size); j = j + 1)
    {
      if(!(i >= j))
        break;

      y[(signed long int)i] = y[(signed long int)i] + y[(signed long int)(i - j)] * (double)-1 * a[(signed long int)j];
    }
  }
}

// double_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 102
double double_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  double *a_ptr;
  double *b_ptr;
  double *w_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j=1;
  for( ; !(j >= Na); j = j + 1)
  {
    double *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    w[0l] = w[0l] - *tmp_post$1 * *tmp_post$2;
  }
  w[0l] = w[0l] + x;
  w[0l] = w[0l] / a[0l];
  w_ptr = &w[0l];
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    double *tmp_post$3=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$4=w_ptr;
    w_ptr = w_ptr + 1l;
    sum = sum + *tmp_post$3 * *tmp_post$4;
  }
  return sum;
}

// double_direct_form_2_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 230
double double_direct_form_2_MSP430(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  double *a_ptr;
  double *b_ptr;
  double *w_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j;
  timer1 = timer1 + 71;
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    double *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    w[0l] = w[0l] - *tmp_post$1 * *tmp_post$2;
    timer1 = timer1 + 54;
  }
  w[0l] = w[0l] + x;
  w[0l] = w[0l] / a[0l];
  w_ptr = &w[0l];
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    double *tmp_post$3=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$4=w_ptr;
    w_ptr = w_ptr + 1l;
    sum = sum + *tmp_post$3 * *tmp_post$4;
    timer1 = timer1 + 46;
  }
  timer1 = timer1 + 38;
  /* assertion (double) timer1 * hw.cycle <= ds.sample_time */
  assert((double)timer1 * hw.cycle <= ds.sample_time);
  if((double)timer1 * hw.cycle <= ds.sample_time)
    (void)0;

  return sum;
}

// double_exp_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 428
void double_exp_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], unsigned int expNumber, double (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  unsigned int k;
  unsigned int l;
  double m2[20l][20l];
  if(expNumber == 0u)
  {
    i = 0u;
    for( ; !(i >= lines); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= columns); j = j + 1u)
        if(i == j)
          result[(signed long int)i][(signed long int)j] = 1.000000;

        else
          result[(signed long int)i][(signed long int)j] = 0.000000;
    }
  }

  else
  {
    i = 0u;
    for( ; !(i >= lines); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= columns); j = j + 1u)
        result[(signed long int)i][(signed long int)j] = m1[(signed long int)i][(signed long int)j];
    }
    if(!(expNumber == 1u))
    {
      l = 1u;
      for( ; !(l >= expNumber); l = l + 1u)
      {
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
            m2[(signed long int)i][(signed long int)j] = result[(signed long int)i][(signed long int)j];
        }
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
            result[(signed long int)i][(signed long int)j] = 0.000000;
        }
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
          {
            k = 0u;
            for( ; !(k >= columns); k = k + 1u)
              result[(signed long int)i][(signed long int)j] = result[(signed long int)i][(signed long int)j] + m2[(signed long int)i][(signed long int)k] * m1[(signed long int)k][(signed long int)j];
          }
        }
      }
    }

  }
}

// double_matrix_multiplication
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 337
void double_matrix_multiplication(unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, double (*m1)[20l], double (*m2)[20l], double (*m3)[20l])
{
  unsigned int i;
  unsigned int j;
  unsigned int k;
  if(j1 == i2)
  {
    i = 0u;
    for( ; !(i >= i1); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= j2); j = j + 1u)
        m3[(signed long int)i][(signed long int)j] = 0.000000;
    }
    i = 0u;
    for( ; !(i >= i1); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= j2); j = j + 1u)
      {
        k = 0u;
        for( ; !(k >= j1); k = k + 1u)
        {
          double mult=m1[(signed long int)i][(signed long int)k] * m2[(signed long int)k][(signed long int)j];
          m3[(signed long int)i][(signed long int)j] = m3[(signed long int)i][(signed long int)j] + m1[(signed long int)i][(signed long int)k] * m2[(signed long int)k][(signed long int)j];
        }
      }
    }
  }

  else
    printf("\nError! Operation invalid, please enter with valid matrices.\n");
}

// double_state_space_representation
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 23
double double_state_space_representation(void)
{
  double result1[20l][20l];
  double result2[20l][20l];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
    {
      result1[(signed long int)i][(signed long int)j] = 0.000000;
      result2[(signed long int)i][(signed long int)j] = 0.000000;
    }
  }
  double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.C, _controller.states, result1);
  double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.D, _controller.inputs, result2);
  double_add_matrix((unsigned int)nOutputs, 1u, result1, result2, _controller.outputs);
  i = 1;
  for( ; !(i >= 0); i = i + 1)
  {
    double_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.A, _controller.states, result1);
    double_matrix_multiplication((unsigned int)nStates, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.B, _controller.inputs, result2);
    double_add_matrix((unsigned int)nStates, 1u, result1, result2, _controller.states);
    double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.C, _controller.states, result1);
    double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.D, _controller.inputs, result2);
    double_add_matrix((unsigned int)nOutputs, 1u, result1, result2, _controller.outputs);
  }
  return _controller.outputs[0l][0l];
}

// double_sub_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 326
void double_sub_matrix(unsigned int lines, unsigned int columns, double (*m1)[20l], double (*m2)[20l], double (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  i = 0u;
  for( ; !(i >= lines); i = i + 1u)
  {
    j = 0u;
    for( ; !(j >= columns); j = j + 1u)
      result[(signed long int)i][(signed long int)j] = m1[(signed long int)i][(signed long int)j] - m2[(signed long int)i][(signed long int)j];
  }
}

// double_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 122
double double_transposed_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  double *a_ptr;
  double *b_ptr;
  double yout=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  double *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  yout = yout / a[0l];
  signed int j=0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      double *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
    }

    if(!(j >= -1 + Nb))
    {
      double *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
    }

  }
  return yout;
}

// double_transposed_direct_form_2_MSP430
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 257
double double_transposed_direct_form_2_MSP430(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  double *a_ptr;
  double *b_ptr;
  double yout=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  double *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  signed int j;
  timer1 = timer1 + 105;
  j = 0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      double *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
      timer1 = timer1 + 41;
    }

    if(!(j >= -1 + Nb))
    {
      double *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
      timer1 = timer1 + 38;
    }

    timer1 = timer1 + 54;
  }
  timer1 = timer1 + 7;
  /* assertion (double) timer1 * hw.cycle <= ds.sample_time */
  assert((double)timer1 * hw.cycle <= ds.sample_time);
  if((double)timer1 * hw.cycle <= ds.sample_time)
    (void)0;

  return yout;
}

// fatorial
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 54
signed int fatorial(signed int n)
{
  signed int tmp_if_expr$2;
  signed int return_value_fatorial$1;
  if(n == 0)
    tmp_if_expr$2 = 1;

  else
  {
    return_value_fatorial$1=fatorial(n - 1);
    tmp_if_expr$2 = n * return_value_fatorial$1;
  }
  return tmp_if_expr$2;
}

// float_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 144
float float_direct_form_1(float *y, float *x, float *a, float *b, signed int Na, signed int Nb)
{
  float *a_ptr;
  float *y_ptr;
  float *b_ptr;
  float *x_ptr;
  float sum=0.000000f;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    float *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    float *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    sum = sum + *tmp_post$1 * *tmp_post$2;
  }
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    float *tmp_post$3=a_ptr;
    a_ptr = a_ptr + 1l;
    float *tmp_post$4=y_ptr;
    y_ptr = y_ptr - 1l;
    sum = sum - *tmp_post$3 * *tmp_post$4;
  }
  sum = sum / a[0l];
  return sum;
}

// float_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 163
float float_direct_form_2(float *w, float x, float *a, float *b, signed int Na, signed int Nb)
{
  float *a_ptr;
  float *b_ptr;
  float *w_ptr;
  float sum=0.000000f;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j=1;
  for( ; !(j >= Na); j = j + 1)
  {
    float *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    float *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    w[0l] = w[0l] - *tmp_post$1 * *tmp_post$2;
  }
  w[0l] = w[0l] + x;
  w[0l] = w[0l] / a[0l];
  w_ptr = &w[0l];
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    float *tmp_post$3=b_ptr;
    b_ptr = b_ptr + 1l;
    float *tmp_post$4=w_ptr;
    w_ptr = w_ptr + 1l;
    sum = sum + *tmp_post$3 * *tmp_post$4;
  }
  return sum;
}

// float_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 183
float float_transposed_direct_form_2(float *w, float x, float *a, float *b, signed int Na, signed int Nb)
{
  float *a_ptr;
  float *b_ptr;
  float yout=0.000000f;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  float *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  yout = yout / a[0l];
  signed int j=0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      float *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
    }

    if(!(j >= -1 + Nb))
    {
      float *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
    }

  }
  return yout;
}

// ft_closedloop_feedback
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 57
void ft_closedloop_feedback(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den)
{
  Nans_num = (Nc_den + Nmodel_num) - 1;
  Nans_den = (Nc_den + Nmodel_den) - 1;
  signed int Nnum_mult=(Nc_num + Nmodel_num) - 1;
  const signed long int Nnum_mult$array_size0=(signed long int)Nans_den;
  double den_mult[Nnum_mult$array_size0];
  const signed long int den_mult$array_size0=(signed long int)Nnum_mult;
  double num_mult[den_mult$array_size0];
  poly_mult(c_num, Nc_num, model_num, Nmodel_num, num_mult, Nnum_mult);
  poly_mult(c_den, Nc_den, model_den, Nmodel_den, den_mult, Nans_den);
  poly_sum(num_mult, Nnum_mult, den_mult, Nans_den, ans_den, Nans_den);
  poly_mult(c_den, Nc_den, model_num, Nmodel_num, ans_num, Nans_num);
}

// ft_closedloop_sensitivity
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 42
void ft_closedloop_sensitivity(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den)
{
  signed int Nans_num_p=(Nc_num + Nmodel_num) - 1;
  Nans_den = (Nc_den + Nmodel_den) - 1;
  Nans_num = (Nc_den + Nmodel_den) - 1;
  const signed long int Nans_num_p$array_size0=(signed long int)Nans_num_p;
  double num_mult[Nans_num_p$array_size0];
  poly_mult(c_den, Nc_den, model_den, Nmodel_den, ans_num, Nans_num);
  poly_mult(c_num, Nc_num, model_num, Nmodel_num, num_mult, Nans_num_p);
  poly_sum(ans_num, Nans_num, num_mult, Nans_num_p, ans_den, Nans_den);
}

// ft_closedloop_series
// file /home/lucascordeiro/dsverifier/bmc/core/closed-loop.h line 28
void ft_closedloop_series(double *c_num, signed int Nc_num, double *c_den, signed int Nc_den, double *model_num, signed int Nmodel_num, double *model_den, signed int Nmodel_den, double *ans_num, signed int Nans_num, double *ans_den, signed int Nans_den)
{
  Nans_num = (Nc_num + Nmodel_num) - 1;
  Nans_den = (Nc_den + Nmodel_den) - 1;
  const signed long int ft_closedloop_series$array_size0=(signed long int)Nans_den;
  double den_mult[ft_closedloop_series$array_size0];
  poly_mult(c_num, Nc_num, model_num, Nmodel_num, ans_num, Nans_num);
  poly_mult(c_den, Nc_den, model_den, Nmodel_den, den_mult, Nans_den);
  poly_sum(ans_num, Nans_num, den_mult, Nans_den, ans_den, Nans_den);
}

// fxp_abs
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 303
signed long int fxp_abs(signed long int a)
{
  signed long int tmp=a < 0l ? -((signed long int)a) : a;
  return tmp;
}

// fxp_add
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 315
signed long int fxp_add(signed long int aadd, signed long int badd)
{
  signed long int tmpadd=(signed long int)aadd + (signed long int)badd;
  return tmpadd;
}

// fxp_add_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 467
void fxp_add_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  i = 0u;
  for( ; !(i >= lines); i = i + 1u)
  {
    j = 0u;
    for( ; !(j >= columns); j = j + 1u)
      result[(signed long int)i][(signed long int)j]=fxp_add(m1[(signed long int)i][(signed long int)j], m2[(signed long int)i][(signed long int)j]);
  }
}

// fxp_check_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 163
void fxp_check_limit_cycle(signed long int *y, signed int y_size)
{
  signed long int reference=y[(signed long int)(y_size - 1)];
  signed int idx=0;
  signed int window_size=1;
  idx = y_size - 2;
  for( ; idx >= 0; idx = idx - 1)
    if(!(y[(signed long int)idx] == reference))
      window_size = window_size + 1;

    else
      break;
  __DSVERIFIER_assume(window_size != y_size && window_size != 1);
  printf("window_size %d\n", window_size);
  signed int desired_elements=2 * window_size;
  signed int found_elements=0;
  idx = y_size - 1;
  for( ; idx >= 0; idx = idx - 1)
    if(!(-1 + y_size + -window_size >= idx))
    {
      printf("%.0f == %.0f\n", y[(signed long int)idx], y[(signed long int)(idx - window_size)]);
      signed int cmp_idx=idx - window_size;
      _Bool tmp_if_expr$1;
      if(cmp_idx >= 1)
        tmp_if_expr$1 = y[(signed long int)idx] == y[(signed long int)(idx - window_size)] ? (_Bool)1 : (_Bool)0;

      else
        tmp_if_expr$1 = (_Bool)0;
      if(tmp_if_expr$1)
        found_elements = found_elements + 2;

      else
        break;
    }

  __DSVERIFIER_assume(found_elements > 0);
  printf("desired_elements %d\n", desired_elements);
  printf("found_elements %d\n", found_elements);
  __DSVERIFIER_assume(found_elements == desired_elements);
  __DSVERIFIER_assert((_Bool)0);
}

// fxp_check_oscillations
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 253
void fxp_check_oscillations(signed long int *y, signed int y_size)
{
  _Bool tmp_if_expr$1;
  if(!(*y == y[(signed long int)(-1 + y_size)]))
    tmp_if_expr$1 = y[(signed long int)(y_size - 1)] != y[(signed long int)(y_size - 2)] ? (_Bool)1 : (_Bool)0;

  else
    tmp_if_expr$1 = (_Bool)0;
  __DSVERIFIER_assume(tmp_if_expr$1);
  signed int window_timer=0;
  signed int window_count=0;
  signed int i;
  signed int j;
  i = 2;
  for( ; !(i >= y_size); i = i + 1)
  {
    signed int window_size=i;
    j = 0;
    for( ; !(j >= y_size); j = j + 1)
    {
      if(!(window_size >= window_timer))
      {
        window_timer = 0;
        window_count = 0;
      }

      signed int window_index=j + window_size;
      if(!(window_index >= y_size))
      {
        if(y[(signed long int)j] == y[(signed long int)window_index])
        {
          window_count = window_count + 1;
          __DSVERIFIER_assert(!(window_count == window_size));
        }

      }

      else
        break;
      window_timer = window_timer + 1;
    }
  }
}

// fxp_check_persistent_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 201
void fxp_check_persistent_limit_cycle(signed long int *y, signed int y_size)
{
  signed int idy=0;
  signed int count_same=0;
  signed int window_size=0;
  signed long int reference=y[0l];
  idy = 0;
  for( ; !(idy >= y_size); idy = idy + 1)
    if(!(y[(signed long int)idy] == reference))
      window_size = window_size + 1;

    else
      if(!(window_size == 0))
        break;

      else
        count_same = count_same + 1;
  window_size = window_size + count_same;
  __DSVERIFIER_assume(window_size > 1 && window_size <= y_size / 2);
  const signed long int reference$array_size0=(signed long int)window_size;
  signed long int lco_elements[reference$array_size0];
  idy = 0;
  for( ; !(idy >= y_size); idy = idy + 1)
    if(!(idy >= window_size))
      lco_elements[(signed long int)idy] = y[(signed long int)idy];

  idy = 0;
  signed int lco_idy=0;
  _Bool is_persistent=(_Bool)0;
  while(!(idy >= y_size))
  {
    signed int tmp_post$1=idy;
    idy = idy + 1;
    signed int tmp_post$2=lco_idy;
    lco_idy = lco_idy + 1;
    if(y[(signed long int)tmp_post$1] == lco_elements[(signed long int)tmp_post$2])
      is_persistent = (_Bool)0;

    else
    {
      is_persistent = (_Bool)0;
      break;
    }
    if(lco_idy == window_size)
      lco_idy = 0;

  }
  __DSVERIFIER_assert((signed int)is_persistent == 0);
}

// fxp_determinant
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 529
double fxp_determinant(signed long int (*a_fxp)[20l], signed int n)
{
  signed int i;
  signed int j;
  signed int j1;
  signed int j2;
  double a[20l][20l];
  i = 0;
  for( ; !(i >= n); i = i + 1)
  {
    j = 0;
    for( ; !(j >= n); j = j + 1)
      a[(signed long int)i][(signed long int)j]=fxp_to_double(a_fxp[(signed long int)i][(signed long int)j]);
  }
  double det=0.000000;
  double m[20l][20l];
  if(n >= 1)
  {
    if(n == 1)
      det = a[0l][0l];

    else
      if(n == 2)
        det = a[0l][0l] * a[1l][1l] - a[1l][0l] * a[0l][1l];

      else
      {
        det = 0.000000;
        j1 = 0;
        for( ; !(j1 >= n); j1 = j1 + 1)
        {
          i = 0;
          for( ; !(i >= -1 + n); i = i + 1)
          {
            i = 1;
            for( ; !(i >= n); i = i + 1)
            {
              j2 = 0;
              j = 0;
              for( ; !(j >= n); j = j + 1)
                if(!(j == j1))
                {
                  m[(signed long int)(i - 1)][(signed long int)j2] = a[(signed long int)i][(signed long int)j];
                  j2 = j2 + 1;
                }

            }
          }
          double return_value_internal_pow$1=internal_pow(-1.000000, 1.000000 + (double)j1 + 1.000000);
          double return_value_determinant$2=determinant(m, n - 1);
          det = det + return_value_internal_pow$1 * a[0l][(signed long int)j1] * return_value_determinant$2;
        }
      }
  }

  return det;
}

// fxp_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 22
signed long int fxp_direct_form_1(signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *y_ptr;
  signed long int *b_ptr;
  signed long int *x_ptr;
  signed long int sum=0l;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    signed long int *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    signed long int *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    signed long int return_value_fxp_mult$3=fxp_mult(*tmp_post$1, *tmp_post$2);
    sum=fxp_add(sum, return_value_fxp_mult$3);
  }
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    signed long int *tmp_post$4=a_ptr;
    a_ptr = a_ptr + 1l;
    signed long int *tmp_post$5=y_ptr;
    y_ptr = y_ptr - 1l;
    signed long int return_value_fxp_mult$6=fxp_mult(*tmp_post$4, *tmp_post$5);
    sum=fxp_sub(sum, return_value_fxp_mult$6);
  }
  sum=fxp_div(sum, a[0l]);
  signed long int return_value_fxp_quantize$7=fxp_quantize(sum);
  return return_value_fxp_quantize$7;
}

// fxp_direct_form_1_impl2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 388
void fxp_direct_form_1_impl2(signed long int *x, signed int x_size, signed long int *b, signed int b_size, signed long int *a, signed int a_size, signed long int *y)
{
  signed int i=0;
  signed int j=0;
  const signed long int j$array_size0=(signed long int)x_size;
  signed long int v[j$array_size0];
  i = 0;
  for( ; !(i >= x_size); i = i + 1)
  {
    v[(signed long int)i] = 0l;
    j = 0;
    for( ; !(j >= b_size); j = j + 1)
    {
      if(!(i >= j))
        break;

      signed long int return_value_fxp_mult$1=fxp_mult(x[(signed long int)(i - j)], b[(signed long int)j]);
      v[(signed long int)i]=fxp_add(v[(signed long int)i], return_value_fxp_mult$1);
    }
  }
  y[0l] = v[0l];
  i = 1;
  for( ; !(i >= x_size); i = i + 1)
  {
    y[(signed long int)i] = 0l;
    y[(signed long int)i]=fxp_add(y[(signed long int)i], v[(signed long int)i]);
    j = 1;
    for( ; !(j >= a_size); j = j + 1)
    {
      if(!(i >= j))
        break;

      signed long int return_value_fxp_mult$2=fxp_mult(y[(signed long int)(i - j)], -a[(signed long int)j]);
      y[(signed long int)i]=fxp_add(y[(signed long int)i], return_value_fxp_mult$2);
    }
  }
}

// fxp_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 41
signed long int fxp_direct_form_2(signed long int *w, signed long int x, signed long int *a, signed long int *b, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *b_ptr;
  signed long int *w_ptr;
  signed long int sum=0l;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j=1;
  for( ; !(j >= Na); j = j + 1)
  {
    signed long int *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    signed long int *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    signed long int return_value_fxp_mult$3=fxp_mult(*tmp_post$1, *tmp_post$2);
    w[0l]=fxp_sub(w[0l], return_value_fxp_mult$3);
  }
  w[0l]=fxp_add(w[0l], x);
  w[0l]=fxp_div(w[0l], a[0l]);
  w_ptr = &w[0l];
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    signed long int *tmp_post$4=b_ptr;
    b_ptr = b_ptr + 1l;
    signed long int *tmp_post$5=w_ptr;
    w_ptr = w_ptr + 1l;
    signed long int return_value_fxp_mult$6=fxp_mult(*tmp_post$4, *tmp_post$5);
    sum=fxp_add(sum, return_value_fxp_mult$6);
  }
  signed long int return_value_fxp_quantize$7=fxp_quantize(sum);
  return return_value_fxp_quantize$7;
}

// fxp_div
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 357
signed long int fxp_div(signed long int a, signed long int b)
{
  signed long int tmpdiv=(a << impl.frac_bits) / b;
  return tmpdiv;
}

// fxp_double_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 211
signed long int fxp_double_to_fxp(double value)
{
  signed long int tmp;
  double ftemp=value * scale_factor[(signed long int)impl.frac_bits];
  if(rounding_mode == 0)
  {
    if(value >= 0.000000)
      tmp = (signed long int)(ftemp + 5.000000e-1);

    else
      tmp = (signed long int)(ftemp - 5.000000e-1);
  }

  else
    if(rounding_mode == 1)
    {
      tmp = (signed long int)ftemp;
      double residue=ftemp - (double)tmp;
      if(value < 0.000000 && IEEE_FLOAT_NOTEQUAL(residue, 0.000000))
      {
        ftemp = ftemp - 1.000000;
        tmp = (signed long int)ftemp;
      }

    }

    else
      if(rounding_mode == 0)
        tmp = (signed long int)ftemp;

  return tmp;
}

// fxp_double_to_fxp_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 247
void fxp_double_to_fxp_array(double *f, signed long int *r, signed int N)
{
  signed int i=0;
  for( ; !(i >= N); i = i + 1)
    r[(signed long int)i]=fxp_double_to_fxp(f[(signed long int)i]);
}

// fxp_exp_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 390
void fxp_exp_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], unsigned int expNumber, signed long int (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  unsigned int l;
  unsigned int k;
  signed long int m2[20l][20l];
  if(expNumber == 0u)
  {
    i = 0u;
    for( ; !(i >= lines); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= columns); j = j + 1u)
        if(i == j)
          result[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(1.000000);

        else
          result[(signed long int)i][(signed long int)j] = 0l;
    }
  }

  else
  {
    i = 0u;
    for( ; !(i >= lines); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= columns); j = j + 1u)
        result[(signed long int)i][(signed long int)j] = m1[(signed long int)i][(signed long int)j];
    }
    if(!(expNumber == 1u))
    {
      l = 1u;
      for( ; !(l >= expNumber); l = l + 1u)
      {
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
            m2[(signed long int)i][(signed long int)j] = result[(signed long int)i][(signed long int)j];
        }
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
            result[(signed long int)i][(signed long int)j] = 0l;
        }
        i = 0u;
        for( ; !(i >= lines); i = i + 1u)
        {
          j = 0u;
          for( ; !(j >= columns); j = j + 1u)
          {
            k = 0u;
            for( ; !(k >= columns); k = k + 1u)
            {
              signed long int return_value_fxp_mult$1=fxp_mult(m2[(signed long int)i][(signed long int)k], m1[(signed long int)k][(signed long int)j]);
              result[(signed long int)i][(signed long int)j]=fxp_add(result[(signed long int)i][(signed long int)j], return_value_fxp_mult$1);
            }
          }
        }
      }
    }

  }
}

// fxp_float_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 198
signed long int fxp_float_to_fxp(float f)
{
  signed long int tmp;
  double ftemp=(double)f * scale_factor[(signed long int)impl.frac_bits];
  if(f >= 0.000000f)
    tmp = (signed long int)(ftemp + 5.000000e-1);

  else
    tmp = (signed long int)(ftemp - 5.000000e-1);
  return tmp;
}

// fxp_float_to_fxp_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 240
void fxp_float_to_fxp_array(float *f, signed long int *r, signed int N)
{
  signed int i=0;
  for( ; !(i >= N); i = i + 1)
    r[(signed long int)i]=fxp_float_to_fxp(f[(signed long int)i]);
}

// fxp_get_frac_part
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 125
signed long int fxp_get_frac_part(signed long int in)
{
  return in < 0l ? -(-in & _fxp_fmask) : in & _fxp_fmask;
}

// fxp_get_int_part
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 115
signed long int fxp_get_int_part(signed long int in)
{
  return in < 0l ? -(-in & _fxp_imask) : in & _fxp_imask;
}

// fxp_int_to_fxp
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 170
signed long int fxp_int_to_fxp(signed int in)
{
  signed long int lin=(signed long int)in * _fxp_one;
  return lin;
}

// fxp_ln
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 288
signed int fxp_ln(signed int x)
{
  signed int t;
  signed int y=0xA65AF;
  if(!(x >= 0x8000))
  {
    x = x << 16;
    y = y - 0xB1721;
  }

  if(!(x >= 0x800000))
  {
    x = x << 8;
    y = y - 0x58B91;
  }

  if(!(x >= 0x8000000))
  {
    x = x << 4;
    y = y - 0x2C5C8;
  }

  if(!(x >= 0x20000000))
  {
    x = x << 2;
    y = y - 0x162E4;
  }

  if(!(x >= 0x40000000))
  {
    x = x << 1;
    y = y - 0xB172;
  }

  t = x + (x >> 1);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x67CD;
  }

  t = x + (x >> 2);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x3920;
  }

  t = x + (x >> 3);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x1E27;
  }

  t = x + (x >> 4);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0xF85;
  }

  t = x + (x >> 5);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x7E1;
  }

  t = x + (x >> 6);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x3F8;
  }

  t = x + (x >> 7);
  if((0x80000000u & (unsigned int)t) == 0u)
  {
    x = t;
    y = y - 0x1FE;
  }

  x = (signed int)(0x80000000u - (unsigned int)x);
  y = y - (x >> 15);
  return y;
}

// fxp_log10
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 345
double fxp_log10(double x)
{
  if(x > 32767.000000)
  {
    if(x > 1.073676e+9)
    {
      x = x / 1.073676e+9;
      double return_value_fxp_log10_low$1=fxp_log10_low(x);
      return return_value_fxp_log10_low$1 + 9.030873e+0;
    }

    x = x / 32767.000000;
    double return_value_fxp_log10_low$2=fxp_log10_low(x);
    return return_value_fxp_log10_low$2 + 4.515437e+0;
  }

  else
  {
    double return_value_fxp_log10_low$3=fxp_log10_low(x);
    return return_value_fxp_log10_low$3;
  }
}

// fxp_log10_low
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 333
double fxp_log10_low(double x)
{
  signed int xint=(signed int)(x * 65536.000000 + 5.000000e-1);
  signed int lnum=fxp_ln(xint);
  signed int lden=fxp_ln(655360);
  return (double)lnum / (double)lden;
}

// fxp_matrix_multiplication
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 368
void fxp_matrix_multiplication(unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*m3)[20l])
{
  unsigned int i;
  unsigned int j;
  unsigned int k;
  if(j1 == i2)
  {
    i = 0u;
    for( ; !(i >= i1); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= j2); j = j + 1u)
        m3[(signed long int)i][(signed long int)j] = 0l;
    }
    i = 0u;
    for( ; !(i >= i1); i = i + 1u)
    {
      j = 0u;
      for( ; !(j >= j2); j = j + 1u)
      {
        k = 0u;
        for( ; !(k >= j1); k = k + 1u)
        {
          signed long int return_value_fxp_mult$1=fxp_mult(m1[(signed long int)i][(signed long int)k], m2[(signed long int)k][(signed long int)j]);
          m3[(signed long int)i][(signed long int)j]=fxp_add(m3[(signed long int)i][(signed long int)j], return_value_fxp_mult$1);
        }
      }
    }
  }

  else
    printf("\nError! Operation invalid, please enter with valid matrices.\n");
}

// fxp_mult
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 339
signed long int fxp_mult(signed long int amult, signed long int bmult)
{
  signed long int tmpmult;
  signed long int tmpmultprec;
  tmpmult = (signed long int)((signed long int)amult * (signed long int)bmult);
  if(tmpmult >= 0l)
    tmpmultprec = tmpmult + ((tmpmult & (signed long int)(1 << impl.frac_bits - 1)) << 1) >> impl.frac_bits;

  else
    tmpmultprec = -(-tmpmult + ((-tmpmult & (signed long int)(1 << impl.frac_bits - 1)) << 1) >> impl.frac_bits);
  return tmpmultprec;
}

// fxp_neg
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 367
signed long int fxp_neg(signed long int aneg)
{
  signed long int tmpneg=-((signed long int)aneg);
  return tmpneg;
}

// fxp_print_float
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 407
void fxp_print_float(signed long int a)
{
  float return_value_fxp_to_float$1=fxp_to_float(a);
  printf("\n%f", return_value_fxp_to_float$1);
}

// fxp_print_float_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 411
void fxp_print_float_array(signed long int *a, signed int N)
{
  signed int i=0;
  for( ; !(i >= N); i = i + 1)
  {
    float return_value_fxp_to_float$1=fxp_to_float(a[(signed long int)i]);
    printf("\n%f", return_value_fxp_to_float$1);
  }
}

// fxp_print_int
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 403
void fxp_print_int(signed long int a)
{
  printf("\n%i", (signed int)a);
}

// fxp_quantize
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 136
signed long int fxp_quantize(signed long int aquant)
{
  if(overflow_mode == 2)
  {
    if(!(aquant >= _fxp_min))
      return _fxp_min;

    else
      if(!(_fxp_max >= aquant))
        return _fxp_max;

  }

  else
    if(overflow_mode == 3)
    {
      if(!(_fxp_max >= aquant) || !(aquant >= _fxp_min))
      {
        signed long int return_value_wrap$1=wrap(aquant, _fxp_min, _fxp_max);
        return return_value_wrap$1;
      }

    }

  return (signed long int)aquant;
}

// fxp_shrl
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 390
signed long int fxp_shrl(signed long int in, signed int shift)
{
  return (signed long int)((unsigned int)in >> shift);
}

// fxp_sign
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 380
signed long int fxp_sign(signed long int a)
{
  return a == 0l ? 0l : (a < 0l ? _fxp_minus_one : _fxp_one);
}

// fxp_square
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 399
signed long int fxp_square(signed long int a)
{
  signed long int return_value_fxp_mult$1=fxp_mult(a, a);
  return return_value_fxp_mult$1;
}

// fxp_state_space_representation
// file /home/lucascordeiro/dsverifier/bmc/core/state-space.h line 67
double fxp_state_space_representation(void)
{
  signed long int result1[20l][20l];
  signed long int result2[20l][20l];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
    {
      result1[(signed long int)i][(signed long int)j] = 0l;
      result2[(signed long int)i][(signed long int)j] = 0l;
    }
  }
  signed long int A_fpx[20l][20l];
  signed long int B_fpx[20l][20l];
  signed long int C_fpx[20l][20l];
  signed long int D_fpx[20l][20l];
  signed long int states_fpx[20l][20l];
  signed long int inputs_fpx[20l][20l];
  signed long int outputs_fpx[20l][20l];
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      A_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      B_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      C_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      D_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      states_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      inputs_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
      outputs_fpx[(signed long int)i][(signed long int)j] = 0l;
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      A_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.A[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      B_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.B[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      C_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.C[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      D_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.D[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      states_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.states[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nInputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      inputs_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.inputs[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      outputs_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.outputs[(signed long int)i][(signed long int)j]);
  }
  fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, C_fpx, states_fpx, result1);
  fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, D_fpx, inputs_fpx, result2);
  fxp_add_matrix((unsigned int)nOutputs, 1u, result1, result2, outputs_fpx);
  i = 1;
  for( ; !(i >= 0); i = i + 1)
  {
    fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, 1u, A_fpx, states_fpx, result1);
    fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)nInputs, (unsigned int)nInputs, 1u, B_fpx, inputs_fpx, result2);
    fxp_add_matrix((unsigned int)nStates, 1u, result1, result2, states_fpx);
    fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, C_fpx, states_fpx, result1);
    fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, D_fpx, inputs_fpx, result2);
    fxp_add_matrix((unsigned int)nOutputs, 1u, result1, result2, outputs_fpx);
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      _controller.states[(signed long int)i][(signed long int)j]=fxp_to_double(states_fpx[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      _controller.outputs[(signed long int)i][(signed long int)j]=fxp_to_double(outputs_fpx[(signed long int)i][(signed long int)j]);
  }
  return _controller.outputs[0l][0l];
}

// fxp_sub
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 327
signed long int fxp_sub(signed long int asub, signed long int bsub)
{
  signed long int tmpsub=(signed long int)((signed long int)asub - (signed long int)bsub);
  return tmpsub;
}

// fxp_sub_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 474
void fxp_sub_matrix(unsigned int lines, unsigned int columns, signed long int (*m1)[20l], signed long int (*m2)[20l], signed long int (*result)[20l])
{
  unsigned int i;
  unsigned int j;
  i = 0u;
  for( ; !(i >= lines); i = i + 1u)
  {
    j = 0u;
    for( ; !(j >= columns); j = j + 1u)
      result[(signed long int)i][(signed long int)j]=fxp_sub(m1[(signed long int)i][(signed long int)j], m2[(signed long int)i][(signed long int)j]);
  }
}

// fxp_to_double
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 271
double fxp_to_double(signed long int fxp)
{
  double f;
  signed int f_int=(signed int)fxp;
  f = (double)f_int * scale_factor_inv[(signed long int)impl.frac_bits];
  return f;
}

// fxp_to_double_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 291
void fxp_to_double_array(double *f, signed long int *r, signed int N)
{
  signed int i=0;
  for( ; !(i >= N); i = i + 1)
    f[(signed long int)i]=fxp_to_double(r[(signed long int)i]);
}

// fxp_to_float
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 264
float fxp_to_float(signed long int fxp)
{
  float f;
  signed int f_int=(signed int)fxp;
  f = (float)((double)f_int * scale_factor_inv[(signed long int)impl.frac_bits]);
  return f;
}

// fxp_to_float_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 284
void fxp_to_float_array(float *f, signed long int *r, signed int N)
{
  signed int i=0;
  for( ; !(i >= N); i = i + 1)
    f[(signed long int)i]=fxp_to_float(r[(signed long int)i]);
}

// fxp_to_int
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 182
signed int fxp_to_int(signed long int fxp)
{
  if(fxp >= 0l)
    fxp = fxp + _fxp_half;

  else
    fxp = fxp - _fxp_half;
  fxp = fxp >> impl.frac_bits;
  return (signed int)fxp;
}

// fxp_transpose
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 582
void fxp_transpose(signed long int (*a)[20l], signed long int (*b)[20l], signed int n, signed int m)
{
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= n); i = i + 1)
  {
    j = 0;
    for( ; !(j >= m); j = j + 1)
      b[(signed long int)j][(signed long int)i] = a[(signed long int)i][(signed long int)j];
  }
}

// fxp_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 61
signed long int fxp_transposed_direct_form_2(signed long int *w, signed long int x, signed long int *a, signed long int *b, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *b_ptr;
  signed long int yout=0l;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  signed long int *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  signed long int return_value_fxp_mult$2=fxp_mult(*tmp_post$1, x);
  yout=fxp_add(return_value_fxp_mult$2, w[0l]);
  yout=fxp_div(yout, a[0l]);
  signed int j=0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      signed long int *tmp_post$3=a_ptr;
      a_ptr = a_ptr + 1l;
      signed long int return_value_fxp_mult$4=fxp_mult(*tmp_post$3, yout);
      w[(signed long int)j]=fxp_sub(w[(signed long int)j], return_value_fxp_mult$4);
    }

    if(!(j >= -1 + Nb))
    {
      signed long int *tmp_post$5=b_ptr;
      b_ptr = b_ptr + 1l;
      signed long int return_value_fxp_mult$6=fxp_mult(*tmp_post$5, x);
      w[(signed long int)j]=fxp_add(w[(signed long int)j], return_value_fxp_mult$6);
    }

  }
  signed long int return_value_fxp_quantize$7=fxp_quantize(yout);
  return return_value_fxp_quantize$7;
}

// fxp_verify_overflow
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 153
void fxp_verify_overflow(signed long int value)
{
  fxp_quantize(value);
  __DSVERIFIER_assert(value <= _fxp_max && value >= _fxp_min);
}

// fxp_verify_overflow_array
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 158
void fxp_verify_overflow_array(signed long int *array, signed int n)
{
  signed int i=0;
  i = 0;
  for( ; !(i >= n); i = i + 1)
    fxp_verify_overflow(array[(signed long int)i]);
}

// generate_delta_coefficients
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 33
void generate_delta_coefficients(double *vetor, double *out, signed int n, double delta)
{
  signed int i;
  signed int j;
  signed int N=n - 1;
  double sum_delta_operator;
  i = 0;
  for( ; N >= i; i = i + 1)
  {
    sum_delta_operator = 0.000000;
    j = 0;
    for( ; i >= j; j = j + 1)
    {
      signed int return_value_nchoosek$1=nchoosek(N - j, i - j);
      sum_delta_operator = sum_delta_operator + vetor[(signed long int)j] * (double)return_value_nchoosek$1;
    }
    double return_value_internal_pow$2=internal_pow(delta, (double)(N - i));
    out[(signed long int)i] = return_value_internal_pow$2 * sum_delta_operator;
  }
}

// generic_timing_double_direct_form_1
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 286
double generic_timing_double_direct_form_1(double *y, double *x, double *a, double *b, signed int Na, signed int Nb)
{
  generic_timer = generic_timer + 6 * hw.assembly.push + 3 * hw.assembly.in + 1 * hw.assembly.sbiw + 1 * hw.assembly.cli + 3 * hw.assembly.out + 12 * hw.assembly.std;
  double *a_ptr;
  double *y_ptr;
  double *b_ptr;
  double *x_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  generic_timer = generic_timer + 12 * hw.assembly.std + 12 * hw.assembly.ldd + 2 * hw.assembly.subi + 2 * hw.assembly.sbci + 4 * hw.assembly.lsl + 4 * hw.assembly.rol + 2 * hw.assembly.add + 2 * hw.assembly.adc + 1 * hw.assembly.adiw;
  signed int i;
  signed int j;
  generic_timer = generic_timer + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    generic_timer = generic_timer + 20 * hw.assembly.ldd + 24 * hw.assembly.mov + 2 * hw.assembly.subi + 1 * hw.assembly.sbci + 1 * hw.assembly.sbc + 10 * hw.assembly.std + 2 * hw.assembly.ld + 2 * hw.assembly.rcall + 1 * hw.assembly.adiw + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.adiw + 1 * hw.assembly.brge + 1 * hw.assembly.rjmp;
    double *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    sum = sum + *tmp_post$1 * *tmp_post$2;
  }
  generic_timer = generic_timer + 2 * hw.assembly.ldi + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    generic_timer = generic_timer + 22 * hw.assembly.ldd + 24 * hw.assembly.mov + 2 * hw.assembly.subi + 8 * hw.assembly.std + 1 * hw.assembly.sbci + 2 * hw.assembly.ld + 2 * hw.assembly.rcall + 1 * hw.assembly.sbc + 1 * hw.assembly.adiw + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.adiw + 1 * hw.assembly.brge + 1 * hw.assembly.rjmp;
    double *tmp_post$3=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$4=y_ptr;
    y_ptr = y_ptr - 1l;
    sum = sum - *tmp_post$3 * *tmp_post$4;
  }
  generic_timer = generic_timer + 4 * hw.assembly.ldd + 4 * hw.assembly.mov + 1 * hw.assembly.adiw + 1 * hw.assembly.in + 1 * hw.assembly.cli + 3 * hw.assembly.out + 6 * hw.assembly.pop + 1 * hw.assembly.ret;
  return sum;
}

// generic_timing_double_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 311
double generic_timing_double_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  generic_timer = generic_timer + 8 * hw.assembly.push + 14 * hw.assembly.std + 3 * hw.assembly.out + 3 * hw.assembly.in + 1 * hw.assembly.sbiw + 1 * hw.assembly.cli;
  double *a_ptr;
  double *b_ptr;
  double *w_ptr;
  double sum=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j;
  generic_timer = generic_timer + 10 * hw.assembly.std + 6 * hw.assembly.ldd + 2 * hw.assembly.adiw;
  generic_timer = generic_timer + 2 * hw.assembly.ldi + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    double *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    double *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    w[0l] = w[0l] - *tmp_post$1 * *tmp_post$2;
    generic_timer = generic_timer + 23 * hw.assembly.ldd + 32 * hw.assembly.mov + 9 * hw.assembly.std + 2 * hw.assembly.subi + 3 * hw.assembly.ld + 2 * hw.assembly.rcall + 2 * hw.assembly.sbci + 1 * hw.assembly.st + 1 * hw.assembly.adiw + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.brge;
  }
  w[0l] = w[0l] + x;
  w_ptr = &w[0l];
  generic_timer = generic_timer + 13 * hw.assembly.ldd + 12 * hw.assembly.mov + 5 * hw.assembly.std + 1 * hw.assembly.st + 1 * hw.assembly.ld + 1 * hw.assembly.rcall;
  generic_timer = generic_timer + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    double *tmp_post$3=b_ptr;
    b_ptr = b_ptr + 1l;
    double *tmp_post$4=w_ptr;
    w_ptr = w_ptr + 1l;
    sum = sum + *tmp_post$3 * *tmp_post$4;
    generic_timer = generic_timer + 20 * hw.assembly.ldd + 24 * hw.assembly.mov + 10 * hw.assembly.std + 2 * hw.assembly.rcall + 2 * hw.assembly.ld + 2 * hw.assembly.subi + 2 * hw.assembly.sbci + 1 * hw.assembly.adiw + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.brge + 1 * hw.assembly.rjmp;
  }
  generic_timer = generic_timer + 4 * hw.assembly.ldd + 4 * hw.assembly.mov + 1 * hw.assembly.adiw + 1 * hw.assembly.in + 1 * hw.assembly.cli + 3 * hw.assembly.out + 8 * hw.assembly.pop + 1 * hw.assembly.ret;
  return sum;
}

// generic_timing_double_transposed_direct_form_2
// file /home/lucascordeiro/dsverifier/bmc/core/realizations.h line 338
double generic_timing_double_transposed_direct_form_2(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  generic_timer = generic_timer + 8 * hw.assembly.push + 14 * hw.assembly.std + 3 * hw.assembly.out + 3 * hw.assembly.in + 1 * hw.assembly.sbiw + 1 * hw.assembly.cli;
  double *a_ptr;
  double *b_ptr;
  double yout=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  double *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  signed int j;
  generic_timer = generic_timer + 15 * hw.assembly.std + 22 * hw.assembly.ldd + 24 * hw.assembly.mov + 2 * hw.assembly.rcall + 2 * hw.assembly.ld + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.subi + 1 * hw.assembly.sbci + 1 * hw.assembly.brge + 1 * hw.assembly.adiw;
  generic_timer = generic_timer + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  j = 0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      double *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
    }

    if(!(j >= -1 + Nb))
    {
      double *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
    }

    generic_timer = generic_timer + 70 * hw.assembly.mov + 65 * hw.assembly.ldd + 12 * hw.assembly.lsl + 12 * hw.assembly.rol + 15 * hw.assembly.std + 6 * hw.assembly.add + 6 * hw.assembly.adc + 2 * hw.assembly.adiw + 3 * hw.assembly.cpc + 3 * hw.assembly.cp + 5 * hw.assembly.ld + 4 * hw.assembly.rcall + 5 * hw.assembly.subi + 3 * hw.assembly.rjmp + 2 * hw.assembly.brlt + 3 * hw.assembly.st + 2 * hw.assembly.sbci + 3 * hw.assembly.sbc + 1 * hw.assembly.brge;
  }
  generic_timer = generic_timer + 4 * hw.assembly.ldd + 4 * hw.assembly.mov + 8 * hw.assembly.pop + 3 * hw.assembly.out + 1 * hw.assembly.in + 1 * hw.assembly.cli + 1 * hw.assembly.adiw + 1 * hw.assembly.ret;
  return yout;
}

// generic_timing_shift_l_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 20
double generic_timing_shift_l_double(double zIn, double *z, signed int N)
{
  generic_timer = generic_timer + 2 * hw.assembly.push + 3 * hw.assembly.in + 3 * hw.assembly.out + 1 * hw.assembly.sbiw + 1 * hw.assembly.cli + 8 * hw.assembly.std;
  signed int i;
  double zOut=z[0l];
  generic_timer = generic_timer + 5 * hw.assembly.ldd + 2 * hw.assembly.mov + 4 * hw.assembly.std + 1 * hw.assembly.ld;
  generic_timer = generic_timer + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
  {
    generic_timer = generic_timer + 17 * hw.assembly.ldd + 4 * hw.assembly.lsl + 4 * hw.assembly.rol + 2 * hw.assembly.add + 2 * hw.assembly.adc + 6 * hw.assembly.mov + 2 * hw.assembly.adiw + 5 * hw.assembly.std + 1 * hw.assembly.ld + 1 * hw.assembly.st + 1 * hw.assembly.subi + 1 * hw.assembly.sbc + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.brlt;
    z[(signed long int)i] = z[(signed long int)(i + 1)];
  }
  z[(signed long int)(N - 1)] = zIn;
  generic_timer = generic_timer + 12 * hw.assembly.ldd + 6 * hw.assembly.mov + 3 * hw.assembly.std + 2 * hw.assembly.lsl + 2 * hw.assembly.rol + 1 * hw.assembly.adc + 1 * hw.assembly.add + 1 * hw.assembly.subi + 1 * hw.assembly.sbci + 1 * hw.assembly.st + 1 * hw.assembly.adiw + 1 * hw.assembly.in + 1 * hw.assembly.cli;
  generic_timer = generic_timer + 3 * hw.assembly.out + 2 * hw.assembly.pop + 1 * hw.assembly.ret;
  return zOut;
}

// generic_timing_shift_r_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 37
double generic_timing_shift_r_double(double zIn, double *z, signed int N)
{
  generic_timer = generic_timer + 2 * hw.assembly.push + 3 * hw.assembly.in + 3 * hw.assembly.out + 1 * hw.assembly.sbiw + 1 * hw.assembly.cli + 8 * hw.assembly.std;
  signed int i;
  double zOut=z[(signed long int)(N - 1)];
  generic_timer = generic_timer + 7 * hw.assembly.ldd + 2 * hw.assembly.rol + 2 * hw.assembly.lsl + 2 * hw.assembly.mov + 4 * hw.assembly.std + 1 * hw.assembly.add + 1 * hw.assembly.adc + 1 * hw.assembly.ld + 1 * hw.assembly.subi + 1 * hw.assembly.sbci;
  generic_timer = generic_timer + 2 * hw.assembly.ldd + 2 * hw.assembly.std + 1 * hw.assembly.sbiw + 1 * hw.assembly.rjmp;
  i = N - 1;
  for( ; i >= 1; i = i - 1)
  {
    z[(signed long int)i] = z[(signed long int)(i - 1)];
    generic_timer = generic_timer + 15 * hw.assembly.ldd + 4 * hw.assembly.lsl + 4 * hw.assembly.rol + 2 * hw.assembly.add + 2 * hw.assembly.adc + 4 * hw.assembly.mov + 5 * hw.assembly.std + 1 * hw.assembly.subi + 1 * hw.assembly.sbci + 1 * hw.assembly.ld + 1 * hw.assembly.st + 1 * hw.assembly.sbiw + 1 * hw.assembly.cp + 1 * hw.assembly.cpc + 1 * hw.assembly.brlt;
  }
  z[0l] = zIn;
  generic_timer = generic_timer + 10 * hw.assembly.ldd + 5 * hw.assembly.mov + 3 * hw.assembly.std + 3 * hw.assembly.out + 2 * hw.assembly.pop + 1 * hw.assembly.ret + 1 * hw.assembly.ret + 1 * hw.assembly.cli + 1 * hw.assembly.in + 1 * hw.assembly.st + 1 * hw.assembly.adiw;
  return zOut;
}

// get_delta_transfer_function
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 52
void get_delta_transfer_function(double *b, double *b_out, signed int b_size, double *a, double *a_out, signed int a_size, double delta)
{
  generate_delta_coefficients(b, b_out, b_size, delta);
  generate_delta_coefficients(a, a_out, a_size, delta);
}

// get_delta_transfer_function_with_base
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 59
void get_delta_transfer_function_with_base(double *b, double *b_out, signed int b_size, double *a, double *a_out, signed int a_size, double delta)
{
  signed int i;
  signed int j;
  signed int N=a_size - 1;
  signed int M=b_size - 1;
  double sum_delta_operator;
  i = 0;
  for( ; N >= i; i = i + 1)
  {
    sum_delta_operator = 0.000000;
    j = 0;
    for( ; i >= j; j = j + 1)
    {
      signed int return_value_nchoosek$1=nchoosek(N - j, i - j);
      sum_delta_operator = sum_delta_operator + a[(signed long int)j] * (double)return_value_nchoosek$1;
    }
    double return_value_internal_pow$2=internal_pow(delta, (double)(N - i));
    a_out[(signed long int)i] = return_value_internal_pow$2 * sum_delta_operator;
  }
  i = 0;
  for( ; M >= i; i = i + 1)
  {
    sum_delta_operator = 0.000000;
    j = 0;
    for( ; i >= j; j = j + 1)
    {
      signed int return_value_nchoosek$3=nchoosek(M - j, i - j);
      sum_delta_operator = sum_delta_operator + b[(signed long int)j] * (double)return_value_nchoosek$3;
    }
    double return_value_internal_pow$4=internal_pow(delta, (double)(M - i));
    b_out[(signed long int)i] = return_value_internal_pow$4 * sum_delta_operator;
  }
}

// iirIIOutTime
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 428
float iirIIOutTime(float *w, float x, float *a, float *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  float *a_ptr;
  float *b_ptr;
  float *w_ptr;
  float sum=0.000000f;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  w_ptr = &w[1l];
  signed int k;
  signed int j;
  timer1 = timer1 + 71;
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    float *tmp_post$1=a_ptr;
    a_ptr = a_ptr + 1l;
    float *tmp_post$2=w_ptr;
    w_ptr = w_ptr + 1l;
    w[0l] = w[0l] - *tmp_post$1 * *tmp_post$2;
    timer1 = timer1 + 54;
  }
  w[0l] = w[0l] + x;
  w_ptr = &w[0l];
  k = 0;
  for( ; !(k >= Nb); k = k + 1)
  {
    float *tmp_post$3=b_ptr;
    b_ptr = b_ptr + 1l;
    float *tmp_post$4=w_ptr;
    w_ptr = w_ptr + 1l;
    sum = sum + *tmp_post$3 * *tmp_post$4;
    timer1 = timer1 + 46;
  }
  timer1 = timer1 + 38;
  /* assertion (double)timer1*CYCLE <= (double)DEADLINE */
  assert(((double)timer1 * 1.000000) / 1.600000e+7 <= 1.000000 / 100.000000);
  if((double)timer1 / 1.600000e+7 <= 1.000000 / 100.000000)
    (void)0;

  return sum;
}

// iirIItOutTime
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 452
float iirIItOutTime(float *w, float x, float *a, float *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  float *a_ptr;
  float *b_ptr;
  float yout=0.000000f;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  float *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  signed int j;
  timer1 = timer1 + 105;
  j = 0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      float *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
      timer1 = timer1 + 41;
    }

    if(!(j >= -1 + Nb))
    {
      float *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
      timer1 = timer1 + 38;
    }

    timer1 = timer1 + 54;
  }
  timer1 = timer1 + 7;
  /* assertion (double)timer1*CYCLE <= (double)DEADLINE */
  assert(((double)timer1 * 1.000000) / 1.600000e+7 <= 1.000000 / 100.000000);
  if((double)timer1 / 1.600000e+7 <= 1.000000 / 100.000000)
    (void)0;

  return yout;
}

// iirIItOutTime_double
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 479
double iirIItOutTime_double(double *w, double x, double *a, double *b, signed int Na, signed int Nb)
{
  signed int timer1=0;
  double *a_ptr;
  double *b_ptr;
  double yout=0.000000;
  a_ptr = &a[1l];
  b_ptr = &b[0l];
  signed int Nw=Na > Nb ? Na : Nb;
  double *tmp_post$1=b_ptr;
  b_ptr = b_ptr + 1l;
  yout = *tmp_post$1 * x + w[0l];
  signed int j;
  timer1 = timer1 + 105;
  j = 0;
  for( ; !(j >= -1 + Nw); j = j + 1)
  {
    w[(signed long int)j] = w[(signed long int)(j + 1)];
    if(!(j >= -1 + Na))
    {
      double *tmp_post$2=a_ptr;
      a_ptr = a_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] - *tmp_post$2 * yout;
      timer1 = timer1 + 41;
    }

    if(!(j >= -1 + Nb))
    {
      double *tmp_post$3=b_ptr;
      b_ptr = b_ptr + 1l;
      w[(signed long int)j] = w[(signed long int)j] + *tmp_post$3 * x;
      timer1 = timer1 + 38;
    }

    timer1 = timer1 + 54;
  }
  timer1 = timer1 + 7;
  /* assertion (double)timer1*CYCLE <= (double)DEADLINE */
  assert(((double)timer1 * 1.000000) / 1.600000e+7 <= 1.000000 / 100.000000);
  if((double)timer1 / 1.600000e+7 <= 1.000000 / 100.000000)
    (void)0;

  return yout;
}

// iirOutBoth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 506
void iirOutBoth(float *yf, float *xf, float *af, float *bf, float *sumf_ref, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int *sum_ref, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *y_ptr;
  signed long int *b_ptr;
  signed long int *x_ptr;
  float *af_ptr;
  float *yf_ptr;
  float *bf_ptr;
  float *xf_ptr;
  signed long int sum=0l;
  float sumf=0.000000f;
  a_ptr = &a[1l];
  y_ptr = &y[(signed long int)(Na - 1)];
  b_ptr = &b[0l];
  x_ptr = &x[(signed long int)(Nb - 1)];
  af_ptr = &af[1l];
  yf_ptr = &yf[(signed long int)(Na - 1)];
  bf_ptr = &bf[0l];
  xf_ptr = &xf[(signed long int)(Nb - 1)];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= Nb); i = i + 1)
  {
    signed long int *tmp_post$1=b_ptr;
    b_ptr = b_ptr + 1l;
    signed long int *tmp_post$2=x_ptr;
    x_ptr = x_ptr - 1l;
    signed long int return_value_fxp_mult$3=fxp_mult(*tmp_post$1, *tmp_post$2);
    sum=fxp_add(sum, return_value_fxp_mult$3);
    float *tmp_post$4=bf_ptr;
    bf_ptr = bf_ptr + 1l;
    float *tmp_post$5=xf_ptr;
    xf_ptr = xf_ptr - 1l;
    sumf = sumf + *tmp_post$4 * *tmp_post$5;
  }
  j = 1;
  for( ; !(j >= Na); j = j + 1)
  {
    signed long int *tmp_post$6=a_ptr;
    a_ptr = a_ptr + 1l;
    signed long int *tmp_post$7=y_ptr;
    y_ptr = y_ptr - 1l;
    signed long int return_value_fxp_mult$8=fxp_mult(*tmp_post$6, *tmp_post$7);
    sum=fxp_sub(sum, return_value_fxp_mult$8);
    float *tmp_post$9=af_ptr;
    af_ptr = af_ptr + 1l;
    float *tmp_post$10=yf_ptr;
    yf_ptr = yf_ptr - 1l;
    sumf = sumf - *tmp_post$9 * *tmp_post$10;
  }
  *sum_ref = sum;
  *sumf_ref = sumf;
}

// iirOutBothL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 586
float iirOutBothL(float *yf, float *xf, float *af, float *bf, float xfin, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int xin, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *y_ptr;
  signed long int *b_ptr;
  signed long int *x_ptr;
  signed long int sum=0l;
  a_ptr = &a[(signed long int)(Na - 1)];
  y_ptr = &y[1l];
  b_ptr = &b[(signed long int)(Nb - 1)];
  x_ptr = &x[0l];
  float *af_ptr;
  float *yf_ptr;
  float *bf_ptr;
  float *xf_ptr;
  float sumf=0.000000f;
  af_ptr = &af[(signed long int)(Na - 1)];
  yf_ptr = &yf[1l];
  bf_ptr = &bf[(signed long int)(Nb - 1)];
  xf_ptr = &xf[0l];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= -1 + Nb); i = i + 1)
  {
    x[(signed long int)i] = x[(signed long int)(i + 1)];
    signed long int *tmp_post$1=b_ptr;
    b_ptr = b_ptr - 1l;
    signed long int *tmp_post$2=x_ptr;
    x_ptr = x_ptr + 1l;
    signed long int return_value_fxp_mult$3=fxp_mult(*tmp_post$1, *tmp_post$2);
    sum=fxp_add(sum, return_value_fxp_mult$3);
    xf[(signed long int)i] = xf[(signed long int)(i + 1)];
    float *tmp_post$4=bf_ptr;
    bf_ptr = bf_ptr - 1l;
    float *tmp_post$5=xf_ptr;
    xf_ptr = xf_ptr + 1l;
    sumf = sumf + *tmp_post$4 * *tmp_post$5;
  }
  x[(signed long int)(Nb - 1)] = xin;
  signed long int *tmp_post$6=b_ptr;
  b_ptr = b_ptr - 1l;
  signed long int *tmp_post$7=x_ptr;
  x_ptr = x_ptr + 1l;
  signed long int return_value_fxp_mult$8=fxp_mult(*tmp_post$6, *tmp_post$7);
  sum=fxp_add(sum, return_value_fxp_mult$8);
  xf[(signed long int)(Nb - 1)] = xfin;
  float *tmp_post$9=bf_ptr;
  bf_ptr = bf_ptr - 1l;
  float *tmp_post$10=xf_ptr;
  xf_ptr = xf_ptr + 1l;
  sumf = sumf + *tmp_post$9 * *tmp_post$10;
  j = 1;
  for( ; !(j >= -1 + Na); j = j + 1)
  {
    signed long int *tmp_post$11=a_ptr;
    a_ptr = a_ptr - 1l;
    signed long int *tmp_post$12=y_ptr;
    y_ptr = y_ptr + 1l;
    signed long int return_value_fxp_mult$13=fxp_mult(*tmp_post$11, *tmp_post$12);
    sum=fxp_sub(sum, return_value_fxp_mult$13);
    y[(signed long int)j] = y[(signed long int)(j + 1)];
    float *tmp_post$14=af_ptr;
    af_ptr = af_ptr - 1l;
    float *tmp_post$15=yf_ptr;
    yf_ptr = yf_ptr + 1l;
    sumf = sumf - *tmp_post$14 * *tmp_post$15;
    yf[(signed long int)j] = yf[(signed long int)(j + 1)];
  }
  signed long int *tmp_post$16;
  signed long int *tmp_post$17;
  signed long int return_value_fxp_mult$18;
  if(Na >= 2)
  {
    tmp_post$16 = a_ptr;
    a_ptr = a_ptr - 1l;
    tmp_post$17 = y_ptr;
    y_ptr = y_ptr + 1l;
    return_value_fxp_mult$18=fxp_mult(*tmp_post$16, *tmp_post$17);
    sum=fxp_sub(sum, return_value_fxp_mult$18);
  }

  y[(signed long int)(Na - 1)] = sum;
  float *tmp_post$19;
  float *tmp_post$20;
  if(Na >= 2)
  {
    tmp_post$19 = af_ptr;
    af_ptr = af_ptr - 1l;
    tmp_post$20 = yf_ptr;
    yf_ptr = yf_ptr + 1l;
    sumf = sumf - *tmp_post$19 * *tmp_post$20;
  }

  yf[(signed long int)(Na - 1)] = sumf;
  float return_value_fxp_to_float$21=fxp_to_float(sum);
  return return_value_fxp_to_float$21 - sumf;
}

// iirOutBothL2
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 626
float iirOutBothL2(float *yf, float *xf, float *af, float *bf, float xfin, signed long int *y, signed long int *x, signed long int *a, signed long int *b, signed long int xin, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *y_ptr;
  signed long int *b_ptr;
  signed long int *x_ptr;
  signed long int sum=0l;
  a_ptr = &a[(signed long int)(Na - 1)];
  y_ptr = &y[1l];
  b_ptr = &b[(signed long int)(Nb - 1)];
  x_ptr = &x[0l];
  float *af_ptr;
  float *yf_ptr;
  float *bf_ptr;
  float *xf_ptr;
  float sumf=0.000000f;
  af_ptr = &af[(signed long int)(Na - 1)];
  yf_ptr = &yf[1l];
  bf_ptr = &bf[(signed long int)(Nb - 1)];
  xf_ptr = &xf[0l];
  signed int i=0;
  signed int j=1;
  i = 0;
  for( ; !(i >= -1 + Nb); i = i + 1)
  {
    x[(signed long int)i] = x[(signed long int)(i + 1)];
    signed long int return_value_fxp_mult$1=fxp_mult(b[(signed long int)((Nb - 1) - i)], x[(signed long int)i]);
    sum=fxp_add(sum, return_value_fxp_mult$1);
    xf[(signed long int)i] = xf[(signed long int)(i + 1)];
    sumf = sumf + bf[(signed long int)((Nb - 1) - i)] * xf[(signed long int)i];
  }
  x[(signed long int)(Nb - 1)] = xin;
  signed long int return_value_fxp_mult$2=fxp_mult(b[(signed long int)((Nb - 1) - i)], x[(signed long int)i]);
  sum=fxp_add(sum, return_value_fxp_mult$2);
  xf[(signed long int)(Nb - 1)] = xfin;
  sumf = sumf + bf[(signed long int)((Nb - 1) - i)] * xf[(signed long int)i];
  j = 1;
  for( ; !(j >= -1 + Na); j = j + 1)
  {
    signed long int return_value_fxp_mult$3=fxp_mult(a[(signed long int)(Na - j)], y[(signed long int)j]);
    sum=fxp_sub(sum, return_value_fxp_mult$3);
    y[(signed long int)j] = y[(signed long int)(j + 1)];
    sumf = sumf - af[(signed long int)(Na - j)] * yf[(signed long int)j];
    yf[(signed long int)j] = yf[(signed long int)(j + 1)];
  }
  signed long int return_value_fxp_mult$4;
  if(Na >= 2)
  {
    return_value_fxp_mult$4=fxp_mult(a[(signed long int)(Na - j)], y[(signed long int)j]);
    sum=fxp_sub(sum, return_value_fxp_mult$4);
  }

  y[(signed long int)(Na - 1)] = sum;
  if(Na >= 2)
    sumf = sumf - af[(signed long int)(Na - j)] * yf[(signed long int)j];

  yf[(signed long int)(Na - 1)] = sumf;
  float return_value_fxp_to_float$5=fxp_to_float(sum);
  return return_value_fxp_to_float$5 - sumf;
}

// iirOutFixedL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 536
signed long int iirOutFixedL(signed long int *y, signed long int *x, signed long int xin, signed long int *a, signed long int *b, signed int Na, signed int Nb)
{
  signed long int *a_ptr;
  signed long int *y_ptr;
  signed long int *b_ptr;
  signed long int *x_ptr;
  signed long int sum=0l;
  a_ptr = &a[(signed long int)(Na - 1)];
  y_ptr = &y[1l];
  b_ptr = &b[(signed long int)(Nb - 1)];
  x_ptr = &x[0l];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= -1 + Nb); i = i + 1)
  {
    x[(signed long int)i] = x[(signed long int)(i + 1)];
    signed long int *tmp_post$1=b_ptr;
    b_ptr = b_ptr - 1l;
    signed long int *tmp_post$2=x_ptr;
    x_ptr = x_ptr + 1l;
    signed long int return_value_fxp_mult$3=fxp_mult(*tmp_post$1, *tmp_post$2);
    sum=fxp_add(sum, return_value_fxp_mult$3);
  }
  x[(signed long int)(Nb - 1)] = xin;
  signed long int *tmp_post$4=b_ptr;
  b_ptr = b_ptr - 1l;
  signed long int *tmp_post$5=x_ptr;
  x_ptr = x_ptr + 1l;
  signed long int return_value_fxp_mult$6=fxp_mult(*tmp_post$4, *tmp_post$5);
  sum=fxp_add(sum, return_value_fxp_mult$6);
  j = 1;
  for( ; !(j >= -1 + Na); j = j + 1)
  {
    signed long int *tmp_post$7=a_ptr;
    a_ptr = a_ptr - 1l;
    signed long int *tmp_post$8=y_ptr;
    y_ptr = y_ptr + 1l;
    signed long int return_value_fxp_mult$9=fxp_mult(*tmp_post$7, *tmp_post$8);
    sum=fxp_sub(sum, return_value_fxp_mult$9);
    y[(signed long int)j] = y[(signed long int)(j + 1)];
  }
  signed long int *tmp_post$10;
  signed long int *tmp_post$11;
  signed long int return_value_fxp_mult$12;
  if(Na >= 2)
  {
    tmp_post$10 = a_ptr;
    a_ptr = a_ptr - 1l;
    tmp_post$11 = y_ptr;
    y_ptr = y_ptr + 1l;
    return_value_fxp_mult$12=fxp_mult(*tmp_post$10, *tmp_post$11);
    sum=fxp_sub(sum, return_value_fxp_mult$12);
  }

  y[(signed long int)(Na - 1)] = sum;
  return sum;
}

// iirOutFloatL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 561
float iirOutFloatL(float *y, float *x, float xin, float *a, float *b, signed int Na, signed int Nb)
{
  float *a_ptr;
  float *y_ptr;
  float *b_ptr;
  float *x_ptr;
  float sum=0.000000f;
  a_ptr = &a[(signed long int)(Na - 1)];
  y_ptr = &y[1l];
  b_ptr = &b[(signed long int)(Nb - 1)];
  x_ptr = &x[0l];
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= -1 + Nb); i = i + 1)
  {
    x[(signed long int)i] = x[(signed long int)(i + 1)];
    float *tmp_post$1=b_ptr;
    b_ptr = b_ptr - 1l;
    float *tmp_post$2=x_ptr;
    x_ptr = x_ptr + 1l;
    sum = sum + *tmp_post$1 * *tmp_post$2;
  }
  x[(signed long int)(Nb - 1)] = xin;
  float *tmp_post$3=b_ptr;
  b_ptr = b_ptr - 1l;
  float *tmp_post$4=x_ptr;
  x_ptr = x_ptr + 1l;
  sum = sum + *tmp_post$3 * *tmp_post$4;
  j = 1;
  for( ; !(j >= -1 + Na); j = j + 1)
  {
    float *tmp_post$5=a_ptr;
    a_ptr = a_ptr - 1l;
    float *tmp_post$6=y_ptr;
    y_ptr = y_ptr + 1l;
    sum = sum - *tmp_post$5 * *tmp_post$6;
    y[(signed long int)j] = y[(signed long int)(j + 1)];
  }
  float *tmp_post$7;
  float *tmp_post$8;
  if(Na >= 2)
  {
    tmp_post$7 = a_ptr;
    a_ptr = a_ptr - 1l;
    tmp_post$8 = y_ptr;
    y_ptr = y_ptr + 1l;
    sum = sum - *tmp_post$7 * *tmp_post$8;
  }

  y[(signed long int)(Na - 1)] = sum;
  return sum;
}

// initialization
// file /home/lucascordeiro/dsverifier/bmc/core/initialization.h line 24
void initialization()
{
  if(impl.frac_bits >= 32)
    printf("impl.frac_bits must be less than word width!\n");

  if(impl.int_bits >= 32 + -impl.frac_bits)
  {
    printf("impl.int_bits must be less than word width subtracted by precision!\n");
    /* assertion 0 */
    assert(0 != 0);
  }

  if(impl.frac_bits >= 31)
    _fxp_one = 2147483647l;

  else
    _fxp_one = (signed long int)(0x1 << impl.frac_bits);
  _fxp_half = (signed long int)(0x1 << impl.frac_bits - 1);
  _fxp_minus_one = (signed long int)-(0x1 << impl.frac_bits);
  _fxp_min = (signed long int)-(0x1 << (impl.frac_bits + impl.int_bits) - 1);
  _fxp_max = (signed long int)((0x1 << (impl.frac_bits + impl.int_bits) - 1) - 1);
  _fxp_fmask = (signed long int)((1 << impl.frac_bits) - 1);
  _fxp_imask = (signed long int)(0x80000000u >> (32 - impl.frac_bits) - 1);
  _dbl_min = (double)_fxp_min;
  _dbl_min = _dbl_min / (double)(1 << impl.frac_bits);
  _dbl_max = (double)_fxp_max;
  _dbl_max = _dbl_max / (double)(1 << impl.frac_bits);
  if(impl.scale == 0 || impl.scale == 1)
    impl.scale = 1;

  else
  {
    if(IEEE_FLOAT_NOTEQUAL(impl.min, 0.000000))
      impl.min = impl.min / (double)impl.scale;

    if(IEEE_FLOAT_NOTEQUAL(impl.max, 0.000000))
      impl.max = impl.max / (double)impl.scale;

  }
}

// initialize_array
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 22
void initialize_array(double *v, signed int n)
{
  signed int i=0;
  for( ; !(i >= n); i = i + 1)
    v[(signed long int)i] = 0.000000;
}

// internal_abs
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 49
double internal_abs(double a)
{
  return a < 0.000000 ? -a : a;
}

// internal_pow
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 39
double internal_pow(double a, double b)
{
  signed int i;
  double acc=1.000000;
  i = 0;
  for( ; (double)i < b; i = i + 1)
    acc = acc * a;
  return acc;
}

// main
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 60
signed int main()
{
  initialization();
  validation();
  rounding_mode = 1;
  call_closedloop_verification_task((void *)verify_stability_closedloop_using_dslib);
  return 0;
}

// nchoosek
// file /home/lucascordeiro/dsverifier/bmc/core/delta-operator.h line 23
signed int nchoosek(signed int n, signed int k)
{
  if(k == 0)
    return 1;

  else
  {
    signed int return_value_nchoosek$1=nchoosek(n - 1, k - 1);
    return (n * return_value_nchoosek$1) / k;
  }
}

// order
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 158
signed int order(signed int Na, signed int Nb)
{
  return Na > Nb ? Na - 1 : Nb - 1;
}

// poly_mult
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 165
void poly_mult(double *a, signed int Na, double *b, signed int Nb, double *ans, signed int Nans)
{
  signed int i;
  signed int j;
  signed int k;
  Nans = (Na + Nb) - 1;
  i = 0;
  for( ; !(i >= Na); i = i + 1)
  {
    j = 0;
    for( ; !(j >= Nb); j = j + 1)
    {
      k = (((Na + Nb) - i) - j) - 2;
      ans[(signed long int)k] = 0.000000;
    }
  }
  i = 0;
  for( ; !(i >= Na); i = i + 1)
  {
    j = 0;
    for( ; !(j >= Nb); j = j + 1)
    {
      k = (((Na + Nb) - i) - j) - 2;
      ans[(signed long int)k] = ans[(signed long int)k] + a[(signed long int)((Na - i) - 1)] * b[(signed long int)((Nb - j) - 1)];
    }
  }
}

// poly_sum
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 141
void poly_sum(double *a, signed int Na, double *b, signed int Nb, double *ans, signed int Nans)
{
  signed int i;
  Nans = Na > Nb ? Na : Nb;
  i = 0;
  for( ; !(i >= Nans); i = i + 1)
    if(!(Nb >= Na))
    {
      ans[(signed long int)i] = a[(signed long int)i];
      if(!(-1 + Na + -Nb >= i))
        ans[(signed long int)i] = ans[(signed long int)i] + b[(signed long int)((i - Na) + Nb)];

    }

    else
    {
      ans[(signed long int)i] = b[(signed long int)i];
      if(!(-1 + Nb + -Na >= i))
        ans[(signed long int)i] = ans[(signed long int)i] + a[(signed long int)((i - Nb) + Na)];

    }
}

// print_array_elements
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 305
void print_array_elements(char *name, double *v, signed int n)
{
  printf("%s = {", name);
  signed int i=0;
  for( ; !(i >= n); i = i + 1)
    printf(" %.32f ", v[(signed long int)i]);
  printf("}\n");
}

// print_fxp_array_elements
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 419
void print_fxp_array_elements(char *name, signed long int *v, signed int n)
{
  printf("%s = {", name);
  signed int i=0;
  for( ; !(i >= n); i = i + 1)
    printf(" %jd ", v[(signed long int)i]);
  printf("}\n");
}

// print_matrix
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 481
void print_matrix(double (*matrix)[20l], unsigned int lines, unsigned int columns)
{
  printf("\nMatrix\n=====================\n\n");
  unsigned int i;
  unsigned int j;
  i = 0u;
  for( ; !(i >= lines); i = i + 1u)
  {
    j = 0u;
    for( ; !(j >= columns); j = j + 1u)
      printf("#matrix[%d][%d]: %2.2f ", i, j, matrix[(signed long int)i][(signed long int)j]);
    printf("\n");
  }
  printf("\n");
}

// rand
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 417
extern signed int rand(void)
{
  next = next * 1103515245ul + 12345ul;
  return (signed int)((unsigned int)(next / 65536ul) % 32768u);
}

// revert_array
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 30
void revert_array(double *v, double *out, signed int n)
{
  initialize_array(out, n);
  signed int i=0;
  for( ; !(i >= n); i = i + 1)
    out[(signed long int)i] = v[(signed long int)((n - i) - 1)];
}

// shiftL
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 53
signed long int shiftL(signed long int zIn, signed long int *z, signed int N)
{
  signed int i;
  signed long int zOut=z[0l];
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
    z[(signed long int)i] = z[(signed long int)(i + 1)];
  z[(signed long int)(N - 1)] = zIn;
  return zOut;
}

// shiftLDouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 119
double shiftLDouble(double zIn, double *z, signed int N)
{
  signed int i;
  double zOut=z[0l];
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
    z[(signed long int)i] = z[(signed long int)(i + 1)];
  z[(signed long int)(N - 1)] = zIn;
  return zOut;
}

// shiftLboth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 130
void shiftLboth(float zfIn, float *zf, signed long int zIn, signed long int *z, signed int N)
{
  signed int i;
  signed long int zOut;
  float zfOut;
  zOut = z[0l];
  zfOut = zf[0l];
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
  {
    z[(signed long int)i] = z[(signed long int)(i + 1)];
    zf[(signed long int)i] = zf[(signed long int)(i + 1)];
  }
  z[(signed long int)(N - 1)] = zIn;
  zf[(signed long int)(N - 1)] = zfIn;
}

// shiftLfloat
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 75
float shiftLfloat(float zIn, float *z, signed int N)
{
  signed int i;
  float zOut=z[0l];
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
    z[(signed long int)i] = z[(signed long int)(i + 1)];
  z[(signed long int)(N - 1)] = zIn;
  return zOut;
}

// shiftR
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 64
signed long int shiftR(signed long int zIn, signed long int *z, signed int N)
{
  signed int i;
  signed long int zOut=z[(signed long int)(N - 1)];
  i = N - 1;
  for( ; i >= 1; i = i - 1)
    z[(signed long int)i] = z[(signed long int)(i - 1)];
  z[0l] = zIn;
  return zOut;
}

// shiftRDdouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 97
double shiftRDdouble(double zIn, double *z, signed int N)
{
  signed int i;
  double zOut=z[0l];
  i = 0;
  for( ; !(i >= -1 + N); i = i + 1)
    z[(signed long int)i] = z[(signed long int)(i + 1)];
  z[(signed long int)(N - 1)] = zIn;
  return zOut;
}

// shiftRboth
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 144
void shiftRboth(float zfIn, float *zf, signed long int zIn, signed long int *z, signed int N)
{
  signed int i;
  signed long int zOut;
  float zfOut;
  zOut = z[(signed long int)(N - 1)];
  zfOut = zf[(signed long int)(N - 1)];
  i = N - 1;
  for( ; i >= 1; i = i - 1)
  {
    z[(signed long int)i] = z[(signed long int)(i - 1)];
    zf[(signed long int)i] = zf[(signed long int)(i - 1)];
  }
  z[0l] = zIn;
  zf[0l] = zfIn;
}

// shiftRdouble
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 108
double shiftRdouble(double zIn, double *z, signed int N)
{
  signed int i;
  double zOut=z[(signed long int)(N - 1)];
  i = N - 1;
  for( ; i >= 1; i = i - 1)
    z[(signed long int)i] = z[(signed long int)(i - 1)];
  z[0l] = zIn;
  return zOut;
}

// shiftRfloat
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 86
float shiftRfloat(float zIn, float *z, signed int N)
{
  signed int i;
  float zOut=z[(signed long int)(N - 1)];
  i = N - 1;
  for( ; i >= 1; i = i - 1)
    z[(signed long int)i] = z[(signed long int)(i - 1)];
  z[0l] = zIn;
  return zOut;
}

// snrPoint
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 402
float snrPoint(float *s, float *n, signed int blksz)
{
  signed int i;
  double ratio=0.000000;
  double power=0.000000;
  i = 0;
  for( ; !(i >= blksz); i = i + 1)
    if(!IEEE_FLOAT_EQUAL(n[(signed long int)i], 0.000000f))
    {
      ratio = (double)(s[(signed long int)i] / n[(signed long int)i]);
      if(!(ratio < -150.000000) && !(ratio > 150.000000))
      {
        power = ratio * ratio;
        /* assertion power >= 1.0f */
        assert(power >= 1.000000);
        if(power >= 1.000000)
          (void)0;

      }

    }

  return 9.999900e+3f;
}

// snrPower
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 381
float snrPower(float *s, float *n, signed int blksz)
{
  signed int i;
  double sv=0.000000;
  double nv=0.000000;
  double snr;
  i = 0;
  for( ; !(i >= blksz); i = i + 1)
  {
    sv = sv + (double)(s[(signed long int)i] * s[(signed long int)i]);
    nv = nv + (double)(n[(signed long int)i] * n[(signed long int)i]);
  }
  if(IEEE_FLOAT_NOTEQUAL(nv, 0.000000))
  {
    /* assertion sv >= nv */
    assert(sv >= nv);
    if(sv >= nv)
      (void)0;

    snr = sv / nv;
    return (float)snr;
  }

  else
    return 9.999900e+3f;
}

// snrVariance
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 357
float snrVariance(float *s, float *n, signed int blksz)
{
  signed int i;
  double sm=0.000000;
  double nm=0.000000;
  double sv=0.000000;
  double nv=0.000000;
  double snr;
  i = 0;
  for( ; !(i >= blksz); i = i + 1)
  {
    sm = sm + (double)s[(signed long int)i];
    nm = nm + (double)n[(signed long int)i];
  }
  sm = sm / (double)blksz;
  nm = nm / (double)blksz;
  i = 0;
  for( ; !(i >= blksz); i = i + 1)
  {
    sv = sv + ((double)s[(signed long int)i] - sm) * ((double)s[(signed long int)i] - sm);
    nv = nv + ((double)n[(signed long int)i] - nm) * ((double)n[(signed long int)i] - nm);
  }
  if(IEEE_FLOAT_NOTEQUAL(nv, 0.000000))
  {
    /* assertion sv >= nv */
    assert(sv >= nv);
    if(sv >= nv)
      (void)0;

    snr = sv / nv;
    return (float)snr;
  }

  else
    return 9.999900e+3f;
}

// srand
// file /home/lucascordeiro/dsverifier/bmc/core/functions.h line 423
extern void srand(unsigned int seed)
{
  next = (unsigned long int)seed;
}

// transpose
// file /home/lucascordeiro/dsverifier/bmc/core/util.h line 571
void transpose(double (*a)[20l], double (*b)[20l], signed int n, signed int m)
{
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= n); i = i + 1)
  {
    j = 0;
    for( ; !(j >= m); j = j + 1)
      b[(signed long int)j][(signed long int)i] = a[(signed long int)i][(signed long int)j];
  }
}

// validation
// file /home/lucascordeiro/dsverifier/bmc/dsverifier.h line 125
void validation()
{
  if(controller.a_size == 0 || plant.b_size == 0 || impl.int_bits == 0)
  {
    printf("\n\n*****************************************************************************************************\n");
    printf("* set (controller, plant, and impl) parameters to check CLOSED LOOP with DSVerifier *\n");
    printf("*****************************************************************************************************\n");
    __DSVERIFIER_assert((_Bool)0);
  }

  else
  {
    printf("\n\n*****************************************************************************************************\n");
    printf("* set (controller and impl) parameters so that they do not overflow *\n");
    printf("*****************************************************************************************************\n");
    unsigned int j=0u;
    for( ; !(j >= (unsigned int)controller.a_size); j = j + 1u)
    {
      const double validation$$1$$6$$2$$1$$1$$value=controller.a[(signed long int)j];
      __DSVERIFIER_assert(validation$$1$$6$$2$$1$$1$$value <= _dbl_max);
      __DSVERIFIER_assert(validation$$1$$6$$2$$1$$1$$value >= _dbl_min);
    }
    j = 0u;
    for( ; !(j >= (unsigned int)controller.b_size); j = j + 1u)
    {
      const double value=controller.b[(signed long int)j];
      __DSVERIFIER_assert(value <= _dbl_max);
      __DSVERIFIER_assert(value >= _dbl_min);
    }
  }
}

// verify_controllability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_controllability.h line 16
signed int verify_controllability(void)
{
  signed int i;
  signed int j;
  signed long int A_fpx[20l][20l];
  signed long int B_fpx[20l][20l];
  signed long int controllabilityMatrix[20l][20l];
  signed long int backup[20l][20l];
  signed long int backupSecond[20l][20l];
  double controllabilityMatrix_double[20l][20l];
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs * nStates); j = j + 1)
    {
      A_fpx[(signed long int)i][(signed long int)j] = 0l;
      B_fpx[(signed long int)i][(signed long int)j] = 0l;
      controllabilityMatrix[(signed long int)i][(signed long int)j] = 0l;
      backup[(signed long int)i][(signed long int)j] = 0l;
      backupSecond[(signed long int)i][(signed long int)j] = 0l;
      controllabilityMatrix_double[(signed long int)i][(signed long int)j] = 0.000000;
    }
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      A_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.A[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      B_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.B[(signed long int)i][(signed long int)j]);
  }
  if(nInputs >= 2)
  {
    signed int l=0;
    j = 0;
    while(!(j >= nInputs * nStates))
    {
      fxp_exp_matrix((unsigned int)nStates, (unsigned int)nStates, A_fpx, (unsigned int)l, backup);
      l = l + 1;
      fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nInputs, backup, B_fpx, backupSecond);
      signed int k=0;
      for( ; !(k >= nInputs); k = k + 1)
      {
        i = 0;
        for( ; !(i >= nStates); i = i + 1)
          controllabilityMatrix[(signed long int)i][(signed long int)j] = backupSecond[(signed long int)i][(signed long int)k];
        j = j + 1;
      }
    }
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nInputs * nStates); j = j + 1)
        backup[(signed long int)i][(signed long int)j] = 0l;
    }
    fxp_transpose(controllabilityMatrix, backup, nStates, nStates * nInputs);
    signed long int mimo_controllabilityMatrix_fxp[20l][20l];
    fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)(nStates * nInputs), (unsigned int)(nStates * nInputs), (unsigned int)nStates, controllabilityMatrix, backup, mimo_controllabilityMatrix_fxp);
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nStates); j = j + 1)
        controllabilityMatrix_double[(signed long int)i][(signed long int)j]=fxp_to_double(mimo_controllabilityMatrix_fxp[(signed long int)i][(signed long int)j]);
    }
    double return_value_determinant$1=determinant(controllabilityMatrix_double, nStates);
    /* assertion determinant(controllabilityMatrix_double,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000))
      (void)0;

  }

  else
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
    {
      fxp_exp_matrix((unsigned int)nStates, (unsigned int)nStates, A_fpx, (unsigned int)j, backup);
      fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nInputs, backup, B_fpx, backupSecond);
      i = 0;
      for( ; !(i >= nStates); i = i + 1)
        controllabilityMatrix[(signed long int)i][(signed long int)j] = backupSecond[(signed long int)i][0l];
    }
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nStates); j = j + 1)
        controllabilityMatrix_double[(signed long int)i][(signed long int)j]=fxp_to_double(controllabilityMatrix[(signed long int)i][(signed long int)j]);
    }
    double return_value_determinant$2=determinant(controllabilityMatrix_double, nStates);
    /* assertion determinant(controllabilityMatrix_double,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000))
      (void)0;

  }
  return 0;
}

// verify_controllability_double
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_controllability.h line 120
signed int verify_controllability_double(void)
{
  signed int i;
  signed int j;
  double controllabilityMatrix[20l][20l];
  double backup[20l][20l];
  double backupSecond[20l][20l];
  double controllabilityMatrix_double[20l][20l];
  if(nInputs >= 2)
  {
    signed int l=0;
    j = 0;
    while(!(j >= nInputs * nStates))
    {
      double_exp_matrix((unsigned int)nStates, (unsigned int)nStates, _controller.A, (unsigned int)l, backup);
      l = l + 1;
      double_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nInputs, backup, _controller.B, backupSecond);
      signed int k=0;
      for( ; !(k >= nInputs); k = k + 1)
      {
        i = 0;
        for( ; !(i >= nStates); i = i + 1)
          controllabilityMatrix[(signed long int)i][(signed long int)j] = backupSecond[(signed long int)i][(signed long int)k];
        j = j + 1;
      }
    }
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nInputs * nStates); j = j + 1)
        backup[(signed long int)i][(signed long int)j] = 0.000000;
    }
    transpose(controllabilityMatrix, backup, nStates, nStates * nInputs);
    double mimo_controllabilityMatrix_double[20l][20l];
    double_matrix_multiplication((unsigned int)nStates, (unsigned int)(nStates * nInputs), (unsigned int)(nStates * nInputs), (unsigned int)nStates, controllabilityMatrix, backup, mimo_controllabilityMatrix_double);
    double return_value_determinant$1=determinant(mimo_controllabilityMatrix_double, nStates);
    /* assertion determinant(mimo_controllabilityMatrix_double,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000))
      (void)0;

  }

  else
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
    {
      double_exp_matrix((unsigned int)nStates, (unsigned int)nStates, _controller.A, (unsigned int)j, backup);
      double_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nInputs, backup, _controller.B, backupSecond);
      i = 0;
      for( ; !(i >= nStates); i = i + 1)
        controllabilityMatrix[(signed long int)i][(signed long int)j] = backupSecond[(signed long int)i][0l];
    }
    double return_value_determinant$2=determinant(controllabilityMatrix, nStates);
    /* assertion determinant(controllabilityMatrix,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000))
      (void)0;

  }
  return 0;
}

// verify_error
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error.h line 20
signed int verify_error(void)
{
  overflow_mode = 2;
  double a_cascade[100l];
  signed int a_cascade_size;
  double b_cascade[100l];
  signed int b_cascade_size;
  signed long int min_fxp=fxp_double_to_fxp(impl.min);
  signed long int max_fxp=fxp_double_to_fxp(impl.max);
  const signed long int max_fxp$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int y[max_fxp$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int x[y$array_size0];
  const signed long int x$array_size0=(signed long int)X_SIZE_VALUE;
  double yf[x$array_size0];
  const signed long int yf$array_size0=(signed long int)X_SIZE_VALUE;
  double xf[yf$array_size0];
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  signed long int yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.b_size;
  signed long int xaux[yaux$array_size0];
  const signed long int xaux$array_size0=(signed long int)Nw;
  signed long int waux[xaux$array_size0];
  const signed long int waux$array_size0=(signed long int)ds.a_size;
  double yfaux[waux$array_size0];
  const signed long int yfaux$array_size0=(signed long int)ds.b_size;
  double xfaux[yfaux$array_size0];
  const signed long int xfaux$array_size0=(signed long int)Nw;
  double wfaux[xfaux$array_size0];
  signed int i=0;
  for( ; !(i >= ds.a_size); i = i + 1)
  {
    yaux[(signed long int)i] = 0l;
    yfaux[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
  {
    xaux[(signed long int)i] = 0l;
    xfaux[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
  {
    waux[(signed long int)i] = 0l;
    wfaux[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    y[(signed long int)i] = 0l;
    signed int return_value_nondet_int$1=nondet_int();
    x[(signed long int)i] = (signed long int)return_value_nondet_int$1;
    _Bool tmp_if_expr$2;
    if(x[(signed long int)i] >= min_fxp)
      tmp_if_expr$2 = x[(signed long int)i] <= max_fxp ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
    yf[(signed long int)i] = 0.000000;
    xf[(signed long int)i]=fxp_to_double(x[(signed long int)i]);
  }
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    double absolute_error;
    double return_value_fxp_to_double$3=fxp_to_double(y[(signed long int)i]);
    absolute_error = yf[(signed long int)i] - return_value_fxp_to_double$3;
    __DSVERIFIER_assert(absolute_error < impl.max_error && absolute_error > -impl.max_error);
  }
  return 0;
}

// verify_error_closedloop
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error_closedloop.h line 27
signed int verify_error_closedloop(void)
{
  overflow_mode = 3;
  double *c_num=controller.b;
  signed int c_num_size=controller.b_size;
  double *c_den=controller.a;
  signed int c_den_size=controller.a_size;
  const signed long int c_den_size$array_size0=(signed long int)controller.b_size;
  signed long int c_num_fxp[c_den_size$array_size0];
  fxp_double_to_fxp_array(c_num, c_num_fxp, controller.b_size);
  const signed long int c_num_fxp$array_size0=(signed long int)controller.a_size;
  signed long int c_den_fxp[c_num_fxp$array_size0];
  fxp_double_to_fxp_array(c_den, c_den_fxp, controller.a_size);
  const signed long int c_den_fxp$array_size0=(signed long int)controller.b_size;
  double c_num_qtz[c_den_fxp$array_size0];
  fxp_to_double_array(c_num_qtz, c_num_fxp, controller.b_size);
  const signed long int c_num_qtz$array_size0=(signed long int)controller.a_size;
  double c_den_qtz[c_num_qtz$array_size0];
  fxp_to_double_array(c_den_qtz, c_den_fxp, controller.a_size);
  double *p_num=plant_cbmc.b;
  signed int p_num_size=plant.b_size;
  double *p_den=plant_cbmc.a;
  signed int p_den_size=plant.a_size;
  double ans_num_double[100l];
  double ans_num_qtz[100l];
  signed int ans_num_size=(controller.b_size + plant.b_size) - 1;
  double ans_den_qtz[100l];
  double ans_den_double[100l];
  signed int ans_den_size=(controller.a_size + plant.a_size) - 1;
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num_qtz, ans_num_size, ans_den_qtz, ans_den_size);
  ft_closedloop_series(c_num, c_num_size, c_den, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num_double, ans_num_size, ans_den_double, ans_den_size);
  signed int i;
  const signed long int i$array_size0=(signed long int)X_SIZE_VALUE;
  double y_qtz[i$array_size0];
  const signed long int y_qtz$array_size0=(signed long int)X_SIZE_VALUE;
  double y_double[y_qtz$array_size0];
  const signed long int y_double$array_size0=(signed long int)X_SIZE_VALUE;
  double x_qtz[y_double$array_size0];
  const signed long int x_qtz$array_size0=(signed long int)X_SIZE_VALUE;
  double x_double[x_qtz$array_size0];
  const signed long int x_double$array_size0=(signed long int)ans_num_size;
  double xaux_qtz[x_double$array_size0];
  const signed long int xaux_qtz$array_size0=(signed long int)ans_num_size;
  double xaux_double[xaux_qtz$array_size0];
  const signed long int xaux_double$array_size0=(signed long int)ans_num_size;
  double xaux[xaux_double$array_size0];
  double nondet_constant_input=nondet_double();
  __DSVERIFIER_assume(nondet_constant_input >= impl.min && nondet_constant_input <= impl.max);
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    x_qtz[(signed long int)i] = nondet_constant_input;
    x_double[(signed long int)i] = nondet_constant_input;
    y_qtz[(signed long int)i] = 0.000000;
    y_double[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= ans_num_size); i = i + 1)
  {
    xaux_qtz[(signed long int)i] = nondet_constant_input;
    xaux_double[(signed long int)i] = nondet_constant_input;
  }
  const signed long int nondet_constant_input$array_size0=(signed long int)ans_den_size;
  double yaux_qtz[nondet_constant_input$array_size0];
  const signed long int yaux_qtz$array_size0=(signed long int)ans_den_size;
  double yaux_double[yaux_qtz$array_size0];
  const signed long int yaux_double$array_size0=(signed long int)ans_den_size;
  double y0_qtz[yaux_double$array_size0];
  const signed long int y0_qtz$array_size0=(signed long int)ans_den_size;
  double y0_double[y0_qtz$array_size0];
  signed int Nw=ans_den_size > ans_num_size ? ans_den_size : ans_num_size;
  const signed long int Nw$array_size0=(signed long int)Nw;
  double waux_qtz[Nw$array_size0];
  const signed long int waux_qtz$array_size0=(signed long int)Nw;
  double waux_double[waux_qtz$array_size0];
  const signed long int waux_double$array_size0=(signed long int)Nw;
  double w0_qtz[waux_double$array_size0];
  const signed long int w0_qtz$array_size0=(signed long int)Nw;
  double w0_double[w0_qtz$array_size0];
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
  {
    waux_qtz[(signed long int)i] = 0.000000;
    waux_double[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    double absolute_error;
    double return_value_fxp_to_double$1=fxp_to_double((signed long int)y_qtz[(signed long int)i]);
    absolute_error = y_double[(signed long int)i] - return_value_fxp_to_double$1;
    __DSVERIFIER_assert(absolute_error < impl.max_error && absolute_error > -impl.max_error);
  }
  return 0;
}

// verify_error_state_space
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_error_state_space.h line 20
signed int verify_error_state_space(void)
{
  overflow_mode = 0;
  struct anonymous$1 __backupController;
  signed int i;
  signed int j;
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      __backupController.A[(signed long int)i][(signed long int)j] = _controller.A[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      __backupController.B[(signed long int)i][(signed long int)j] = _controller.B[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      __backupController.C[(signed long int)i][(signed long int)j] = _controller.C[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      __backupController.D[(signed long int)i][(signed long int)j] = _controller.D[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      __backupController.states[(signed long int)i][(signed long int)j] = _controller.states[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nInputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      __backupController.inputs[(signed long int)i][(signed long int)j] = _controller.inputs[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      __backupController.outputs[(signed long int)i][(signed long int)j] = _controller.outputs[(signed long int)i][(signed long int)j];
  }
  double __quant_error=0.000000;
  double output_double=double_state_space_representation();
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      _controller.A[(signed long int)i][(signed long int)j] = __backupController.A[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      _controller.B[(signed long int)i][(signed long int)j] = __backupController.B[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      _controller.C[(signed long int)i][(signed long int)j] = __backupController.C[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nInputs); j = j + 1)
      _controller.D[(signed long int)i][(signed long int)j] = __backupController.D[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      _controller.states[(signed long int)i][(signed long int)j] = __backupController.states[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nInputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      _controller.inputs[(signed long int)i][(signed long int)j] = __backupController.inputs[(signed long int)i][(signed long int)j];
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 1); j = j + 1)
      _controller.outputs[(signed long int)i][(signed long int)j] = __backupController.outputs[(signed long int)i][(signed long int)j];
  }
  double output_fxp=fxp_state_space_representation();
  fxp_verify_overflow((signed long int)output_fxp);
  __quant_error = ((output_fxp - output_double) / output_double) * 100.000000;
  /* assertion __quant_error < error_limit && __quant_error > (-error_limit) */
  assert(__quant_error < error_limit && __quant_error > -error_limit);
  if(__quant_error < error_limit && __quant_error > -error_limit)
    (void)0;

  return 0;
}

// verify_generic_timing
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_generic_timing.h line 25
signed int verify_generic_timing(void)
{
  const signed long int verify_generic_timing$array_size0=(signed long int)X_SIZE_VALUE;
  double y[verify_generic_timing$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  double x[y$array_size0];
  signed int i=0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    y[(signed long int)i] = 0.000000;
    float return_value_nondet_float$1=nondet_float();
    x[(signed long int)i] = (double)return_value_nondet_float$1;
    _Bool tmp_if_expr$2;
    if(x[(signed long int)i] >= impl.min)
      tmp_if_expr$2 = x[(signed long int)i] <= impl.max ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
  }
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  double yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.b_size;
  double xaux[yaux$array_size0];
  const signed long int xaux$array_size0=(signed long int)Nw;
  double waux[xaux$array_size0];
  i = 0;
  for( ; !(i >= ds.a_size); i = i + 1)
    yaux[(signed long int)i] = 0.000000;
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
    xaux[(signed long int)i] = 0.000000;
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
    waux[(signed long int)i] = 0.000000;
  double xk;
  double temp;
  double *aptr;
  double *bptr;
  double *xptr;
  double *yptr;
  double *wptr;
  signed int j;
  generic_timer = generic_timer + 2 * hw.assembly.std + 1 * hw.assembly.rjmp;
  double initial_timer=(double)generic_timer;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    generic_timer = generic_timer + 2 * hw.assembly.ldd + 1 * hw.assembly.adiw + 2 * hw.assembly.std;
    generic_timer = generic_timer + 2 * hw.assembly.ldd + 1 * hw.assembly.cpi + 1 * hw.assembly.cpc + 1 * hw.assembly.brlt;
    double spent_time=(double)generic_timer * hw.cycle;
    /* assertion spent_time <= ds.sample_time */
    assert(spent_time <= ds.sample_time);
    if(spent_time <= ds.sample_time)
      (void)0;

    generic_timer = (signed int)initial_timer;
  }
  return 0;
}

// verify_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle.h line 111
signed int verify_limit_cycle(void)
{
  overflow_mode = 3;
  signed int i;
  signed int Set_xsize_at_least_two_times_Na=2 * ds.a_size;
  printf("X_SIZE must be at least 2 * ds.a_size");
  __DSVERIFIER_assert(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na);
  const signed long int Set_xsize_at_least_two_times_Na$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int y[Set_xsize_at_least_two_times_Na$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int x[y$array_size0];
  signed long int min_fxp=fxp_double_to_fxp(impl.min);
  signed long int max_fxp=fxp_double_to_fxp(impl.max);
  const signed long int max_fxp$array_size0=(signed long int)ds.b_size;
  signed long int xaux[max_fxp$array_size0];
  signed int nondet_constant_input=nondet_int();
  __DSVERIFIER_assume((signed long int)nondet_constant_input >= min_fxp && (signed long int)nondet_constant_input <= max_fxp);
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    x[(signed long int)i] = (signed long int)nondet_constant_input;
    y[(signed long int)i] = 0l;
  }
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
    xaux[(signed long int)i] = (signed long int)nondet_constant_input;
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  signed long int yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.a_size;
  signed long int y0[yaux$array_size0];
  const signed long int y0$array_size0=(signed long int)Nw;
  signed long int waux[y0$array_size0];
  const signed long int waux$array_size0=(signed long int)Nw;
  signed long int w0[waux$array_size0];
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
  {
    signed int return_value_nondet_int$1=nondet_int();
    waux[(signed long int)i] = (signed long int)return_value_nondet_int$1;
    _Bool tmp_if_expr$2;
    if(waux[(signed long int)i] >= min_fxp)
      tmp_if_expr$2 = waux[(signed long int)i] <= max_fxp ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
    w0[(signed long int)i] = waux[(signed long int)i];
  }
  signed long int xk;
  signed long int temp;
  signed long int *aptr;
  signed long int *bptr;
  signed long int *xptr;
  signed long int *yptr;
  signed long int *wptr;
  signed int j;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
    ;
  fxp_check_persistent_limit_cycle(y, X_SIZE_VALUE);
  return 0;
}

// verify_limit_cycle_closed_loop
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle_closedloop.h line 29
signed int verify_limit_cycle_closed_loop(void)
{
  overflow_mode = 3;
  double *c_num=controller.b;
  signed int c_num_size=controller.b_size;
  double *c_den=controller.a;
  signed int c_den_size=controller.a_size;
  const signed long int c_den_size$array_size0=(signed long int)controller.b_size;
  signed long int c_num_fxp[c_den_size$array_size0];
  fxp_double_to_fxp_array(c_num, c_num_fxp, controller.b_size);
  const signed long int c_num_fxp$array_size0=(signed long int)controller.a_size;
  signed long int c_den_fxp[c_num_fxp$array_size0];
  fxp_double_to_fxp_array(c_den, c_den_fxp, controller.a_size);
  const signed long int c_den_fxp$array_size0=(signed long int)controller.b_size;
  double c_num_qtz[c_den_fxp$array_size0];
  fxp_to_double_array(c_num_qtz, c_num_fxp, controller.b_size);
  const signed long int c_num_qtz$array_size0=(signed long int)controller.a_size;
  double c_den_qtz[c_num_qtz$array_size0];
  fxp_to_double_array(c_den_qtz, c_den_fxp, controller.a_size);
  double *p_num=plant_cbmc.b;
  signed int p_num_size=plant.b_size;
  double *p_den=plant_cbmc.a;
  signed int p_den_size=plant.a_size;
  double ans_num[100l];
  signed int ans_num_size=(controller.b_size + plant.b_size) - 1;
  double ans_den[100l];
  signed int ans_den_size=(controller.a_size + plant.a_size) - 1;
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den, ans_den_size);
  signed int i;
  const signed long int i$array_size0=(signed long int)X_SIZE_VALUE;
  double y[i$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  double x[y$array_size0];
  const signed long int x$array_size0=(signed long int)ans_num_size;
  double xaux[x$array_size0];
  double nondet_constant_input=nondet_double();
  __DSVERIFIER_assume(nondet_constant_input >= impl.min && nondet_constant_input <= impl.max);
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    x[(signed long int)i] = nondet_constant_input;
    y[(signed long int)i] = 0.000000;
  }
  i = 0;
  for( ; !(i >= ans_num_size); i = i + 1)
    xaux[(signed long int)i] = nondet_constant_input;
  const signed long int nondet_constant_input$array_size0=(signed long int)ans_den_size;
  double yaux[nondet_constant_input$array_size0];
  const signed long int yaux$array_size0=(signed long int)ans_den_size;
  double y0[yaux$array_size0];
  signed int Nw=ans_den_size > ans_num_size ? ans_den_size : ans_num_size;
  const signed long int Nw$array_size0=(signed long int)Nw;
  double waux[Nw$array_size0];
  const signed long int waux$array_size0=(signed long int)Nw;
  double w0[waux$array_size0];
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
  {
    signed int return_value_nondet_int$1=nondet_int();
    waux[(signed long int)i] = (double)return_value_nondet_int$1;
    _Bool tmp_if_expr$2;
    if(waux[(signed long int)i] >= impl.min)
      tmp_if_expr$2 = waux[(signed long int)i] <= impl.max ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
    w0[(signed long int)i] = waux[(signed long int)i];
  }
  double xk;
  double temp;
  double *aptr;
  double *bptr;
  double *xptr;
  double *yptr;
  double *wptr;
  signed int j;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
    ;
  double_check_persistent_limit_cycle(y, X_SIZE_VALUE);
  return 0;
}

// verify_limit_cycle_state_space
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_limit_cycle.h line 21
signed int verify_limit_cycle_state_space(void)
{
  double stateMatrix[20l][20l];
  double outputMatrix[20l][20l];
  double arrayLimitCycle[20l];
  double result1[20l][20l];
  double result2[20l][20l];
  signed int i;
  signed int j;
  signed int k;
  i = 0;
  for( ; !(i >= 20); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 20); j = j + 1)
    {
      result1[(signed long int)i][(signed long int)j] = 0.000000;
      result2[(signed long int)i][(signed long int)j] = 0.000000;
      stateMatrix[(signed long int)i][(signed long int)j] = 0.000000;
      outputMatrix[(signed long int)i][(signed long int)j] = 0.000000;
    }
  }
  double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.C, _controller.states, result1);
  double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.D, _controller.inputs, result2);
  double_add_matrix((unsigned int)nOutputs, 1u, result1, result2, _controller.outputs);
  k = 0;
  i = 1;
  for( ; !(i >= 0); i = i + 1)
  {
    double_matrix_multiplication((unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.A, _controller.states, result1);
    double_matrix_multiplication((unsigned int)nStates, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.B, _controller.inputs, result2);
    double_add_matrix((unsigned int)nStates, 1u, result1, result2, _controller.states);
    double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, 1u, _controller.C, _controller.states, result1);
    double_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nInputs, (unsigned int)nInputs, 1u, _controller.D, _controller.inputs, result2);
    double_add_matrix((unsigned int)nOutputs, 1u, result1, result2, _controller.outputs);
    signed int l=0;
    for( ; !(l >= nStates); l = l + 1)
      stateMatrix[(signed long int)l][(signed long int)k] = _controller.states[(signed long int)l][0l];
    l = 0;
    for( ; !(l >= nOutputs); l = l + 1)
      stateMatrix[(signed long int)l][(signed long int)k] = _controller.outputs[(signed long int)l][0l];
    k = k + 1;
  }
  printf("#matrix STATES -------------------------------");
  print_matrix(stateMatrix, (unsigned int)nStates, 0u);
  printf("#matrix OUTPUTS -------------------------------");
  print_matrix(outputMatrix, (unsigned int)nOutputs, 0u);
  /* assertion 0 */
  assert(0 != 0);
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 0); j = j + 1)
      arrayLimitCycle[(signed long int)j] = stateMatrix[(signed long int)i][(signed long int)j];
    double_check_persistent_limit_cycle(arrayLimitCycle, 0);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= 0); j = j + 1)
      arrayLimitCycle[(signed long int)j] = outputMatrix[(signed long int)i][(signed long int)j];
    double_check_persistent_limit_cycle(arrayLimitCycle, 0);
  }
  /* assertion 0 */
  assert(0 != 0);
}

// verify_minimum_phase
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_minimum_phase.h line 24
signed int verify_minimum_phase(void)
{
  overflow_mode = 0;
  return 0;
}

// verify_observability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_observability.h line 19
signed int verify_observability(void)
{
  signed int i;
  signed int j;
  signed long int A_fpx[20l][20l];
  signed long int C_fpx[20l][20l];
  signed long int observabilityMatrix[20l][20l];
  signed long int backup[20l][20l];
  signed long int backupSecond[20l][20l];
  double observabilityMatrix_double[20l][20l];
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
    {
      observabilityMatrix[(signed long int)i][(signed long int)j] = 0l;
      A_fpx[(signed long int)i][(signed long int)j] = 0l;
      C_fpx[(signed long int)i][(signed long int)j] = 0l;
      backup[(signed long int)i][(signed long int)j] = 0l;
      backupSecond[(signed long int)i][(signed long int)j] = 0l;
    }
  }
  i = 0;
  for( ; !(i >= nStates); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      A_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.A[(signed long int)i][(signed long int)j]);
  }
  i = 0;
  for( ; !(i >= nOutputs); i = i + 1)
  {
    j = 0;
    for( ; !(j >= nStates); j = j + 1)
      C_fpx[(signed long int)i][(signed long int)j]=fxp_double_to_fxp(_controller.C[(signed long int)i][(signed long int)j]);
  }
  if(nOutputs >= 2)
  {
    signed int l;
    j = 0;
    l = 0;
    while(!(l >= nStates))
    {
      fxp_exp_matrix((unsigned int)nStates, (unsigned int)nStates, A_fpx, (unsigned int)l, backup);
      l = l + 1;
      fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, C_fpx, backup, backupSecond);
      signed int k=0;
      for( ; !(k >= nOutputs); k = k + 1)
      {
        i = 0;
        for( ; !(i >= nStates); i = i + 1)
          observabilityMatrix[(signed long int)j][(signed long int)i] = backupSecond[(signed long int)k][(signed long int)i];
        j = j + 1;
      }
    }
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nOutputs * nStates); j = j + 1)
        backup[(signed long int)i][(signed long int)j] = 0l;
    }
    fxp_transpose(observabilityMatrix, backup, nStates * nOutputs, nStates);
    signed long int mimo_observabilityMatrix_fxp[20l][20l];
    fxp_matrix_multiplication((unsigned int)nStates, (unsigned int)(nStates * nOutputs), (unsigned int)(nStates * nOutputs), (unsigned int)nStates, backup, observabilityMatrix, mimo_observabilityMatrix_fxp);
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nStates); j = j + 1)
        observabilityMatrix_double[(signed long int)i][(signed long int)j]=fxp_to_double(mimo_observabilityMatrix_fxp[(signed long int)i][(signed long int)j]);
    }
    double return_value_determinant$1=determinant(observabilityMatrix_double, nStates);
    /* assertion determinant(observabilityMatrix_double,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$1, 0.000000))
      (void)0;

  }

  else
  {
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      fxp_exp_matrix((unsigned int)nStates, (unsigned int)nStates, A_fpx, (unsigned int)i, backup);
      fxp_matrix_multiplication((unsigned int)nOutputs, (unsigned int)nStates, (unsigned int)nStates, (unsigned int)nStates, C_fpx, backup, backupSecond);
      j = 0;
      for( ; !(j >= nStates); j = j + 1)
        observabilityMatrix[(signed long int)i][(signed long int)j] = backupSecond[0l][(signed long int)j];
    }
    i = 0;
    for( ; !(i >= nStates); i = i + 1)
    {
      j = 0;
      for( ; !(j >= nStates); j = j + 1)
        observabilityMatrix_double[(signed long int)i][(signed long int)j]=fxp_to_double(observabilityMatrix[(signed long int)i][(signed long int)j]);
    }
    double return_value_determinant$2=determinant(observabilityMatrix_double, nStates);
    /* assertion determinant(observabilityMatrix_double,nStates) != 0 */
    assert(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000));
    if(IEEE_FLOAT_NOTEQUAL(return_value_determinant$2, 0.000000))
      (void)0;

  }
  return 0;
}

// verify_overflow
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_overflow.h line 23
signed int verify_overflow(void)
{
  overflow_mode = 1;
  signed long int min_fxp=fxp_double_to_fxp(impl.min);
  signed long int max_fxp=fxp_double_to_fxp(impl.max);
  const signed long int max_fxp$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int y[max_fxp$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int x[y$array_size0];
  signed int i=0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    y[(signed long int)i] = 0l;
    signed int return_value_nondet_int$1=nondet_int();
    x[(signed long int)i] = (signed long int)return_value_nondet_int$1;
    _Bool tmp_if_expr$2;
    if(x[(signed long int)i] >= min_fxp)
      tmp_if_expr$2 = x[(signed long int)i] <= max_fxp ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
  }
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  signed long int yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.b_size;
  signed long int xaux[yaux$array_size0];
  const signed long int xaux$array_size0=(signed long int)Nw;
  signed long int waux[xaux$array_size0];
  i = 0;
  for( ; !(i >= ds.a_size); i = i + 1)
    yaux[(signed long int)i] = 0l;
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
    xaux[(signed long int)i] = 0l;
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
    waux[(signed long int)i] = 0l;
  signed long int xk;
  signed long int temp;
  signed long int *aptr;
  signed long int *bptr;
  signed long int *xptr;
  signed long int *yptr;
  signed long int *wptr;
  signed int j;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
    ;
  fxp_verify_overflow_array(y, X_SIZE_VALUE);
  return 0;
}

// verify_stability
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_stability.h line 24
signed int verify_stability(void)
{
  overflow_mode = 0;
  return 0;
}

// verify_stability_closedloop_using_dslib
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_stability_closedloop.h line 21
signed int verify_stability_closedloop_using_dslib(void)
{
  double *c_num=controller.b;
  signed int c_num_size=controller.b_size;
  double *c_den=controller.a;
  signed int c_den_size=controller.a_size;
  const signed long int c_den_size$array_size0=(signed long int)controller.b_size;
  signed long int c_num_fxp[c_den_size$array_size0];
  fxp_double_to_fxp_array(c_num, c_num_fxp, controller.b_size);
  const signed long int c_num_fxp$array_size0=(signed long int)controller.a_size;
  signed long int c_den_fxp[c_num_fxp$array_size0];
  fxp_double_to_fxp_array(c_den, c_den_fxp, controller.a_size);
  const signed long int c_den_fxp$array_size0=(signed long int)controller.b_size;
  double c_num_qtz[c_den_fxp$array_size0];
  fxp_to_double_array(c_num_qtz, c_num_fxp, controller.b_size);
  const signed long int c_num_qtz$array_size0=(signed long int)controller.a_size;
  double c_den_qtz[c_num_qtz$array_size0];
  fxp_to_double_array(c_den_qtz, c_den_fxp, controller.a_size);
  double *p_num=plant_cbmc.b;
  signed int p_num_size=plant.b_size;
  double *p_den=plant_cbmc.a;
  signed int p_den_size=plant.a_size;
  double ans_num[100l];
  signed int ans_num_size=(controller.b_size + plant.b_size) - 1;
  double ans_den[100l];
  signed int ans_den_size=(controller.a_size + plant.a_size) - 1;
  ft_closedloop_series(c_num_qtz, c_num_size, c_den_qtz, c_den_size, p_num, p_num_size, p_den, p_den_size, ans_num, ans_num_size, ans_den, ans_den_size);
  printf("Verifying stability for closedloop function\n");
  signed int return_value_check_stability_closedloop$1=check_stability_closedloop(ans_den, ans_den_size, p_num, p_num_size, p_den, p_den_size);
  __DSVERIFIER_assert((_Bool)return_value_check_stability_closedloop$1);
  return 0;
}

// verify_timing_msp_430
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_timing_msp430.h line 22
signed int verify_timing_msp_430(void)
{
  const signed long int verify_timing_msp_430$array_size0=(signed long int)X_SIZE_VALUE;
  double y[verify_timing_msp_430$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  double x[y$array_size0];
  signed int i=0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    y[(signed long int)i] = 0.000000;
    float return_value_nondet_float$1=nondet_float();
    x[(signed long int)i] = (double)return_value_nondet_float$1;
    _Bool tmp_if_expr$2;
    if(x[(signed long int)i] >= impl.min)
      tmp_if_expr$2 = x[(signed long int)i] <= impl.max ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
  }
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  double yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.b_size;
  double xaux[yaux$array_size0];
  const signed long int xaux$array_size0=(signed long int)Nw;
  double waux[xaux$array_size0];
  i = 0;
  for( ; !(i >= ds.a_size); i = i + 1)
    yaux[(signed long int)i] = 0.000000;
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
    xaux[(signed long int)i] = 0.000000;
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
    waux[(signed long int)i] = 0.000000;
  double xk;
  double temp;
  double *aptr;
  double *bptr;
  double *xptr;
  double *yptr;
  double *wptr;
  signed int j;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
    ;
  return 0;
}

// verify_zero_input_limit_cycle
// file /home/lucascordeiro/dsverifier/bmc/engine/verify_zero_input_limit_cycle.h line 16
signed int verify_zero_input_limit_cycle(void)
{
  overflow_mode = 3;
  signed int i;
  signed int j;
  signed int Set_xsize_at_least_two_times_Na=2 * ds.a_size;
  printf("X_SIZE must be at least 2 * ds.a_size");
  /* assertion X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na */
  assert(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na);
  if(X_SIZE_VALUE >= Set_xsize_at_least_two_times_Na)
    (void)0;

  signed long int min_fxp=fxp_double_to_fxp(impl.min);
  signed long int max_fxp=fxp_double_to_fxp(impl.max);
  const signed long int max_fxp$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int y[max_fxp$array_size0];
  const signed long int y$array_size0=(signed long int)X_SIZE_VALUE;
  signed long int x[y$array_size0];
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
  {
    y[(signed long int)i] = 0l;
    x[(signed long int)i] = 0l;
  }
  signed int Nw=0;
  Nw = ds.a_size > ds.b_size ? ds.a_size : ds.b_size;
  const signed long int Nw$array_size0=(signed long int)ds.a_size;
  signed long int yaux[Nw$array_size0];
  const signed long int yaux$array_size0=(signed long int)ds.b_size;
  signed long int xaux[yaux$array_size0];
  const signed long int xaux$array_size0=(signed long int)Nw;
  signed long int waux[xaux$array_size0];
  const signed long int waux$array_size0=(signed long int)ds.a_size;
  signed long int y0[waux$array_size0];
  const signed long int y0$array_size0=(signed long int)Nw;
  signed long int w0[y0$array_size0];
  i = 0;
  for( ; !(i >= Nw); i = i + 1)
  {
    signed int return_value_nondet_int$1=nondet_int();
    waux[(signed long int)i] = (signed long int)return_value_nondet_int$1;
    _Bool tmp_if_expr$2;
    if(waux[(signed long int)i] >= min_fxp)
      tmp_if_expr$2 = waux[(signed long int)i] <= max_fxp ? (_Bool)1 : (_Bool)0;

    else
      tmp_if_expr$2 = (_Bool)0;
    __DSVERIFIER_assume(tmp_if_expr$2);
    w0[(signed long int)i] = waux[(signed long int)i];
  }
  i = 0;
  for( ; !(i >= ds.b_size); i = i + 1)
    xaux[(signed long int)i] = 0l;
  signed long int xk;
  signed long int temp;
  signed long int *aptr;
  signed long int *bptr;
  signed long int *xptr;
  signed long int *yptr;
  signed long int *wptr;
  i = 0;
  for( ; !(i >= X_SIZE_VALUE); i = i + 1)
    ;
  fxp_check_persistent_limit_cycle(y, X_SIZE_VALUE);
  return 0;
}

// wrap
// file /home/lucascordeiro/dsverifier/bmc/core/fixed-point.h line 100
signed long int wrap(signed long int kX, signed long int kLowerBound, signed long int kUpperBound)
{
  signed int range_size=(signed int)((kUpperBound - kLowerBound) + 1l);
  if(!(kX >= kLowerBound))
    kX = kX + (signed long int)range_size * ((kLowerBound - kX) / (signed long int)range_size + 1l);

  return kLowerBound + (kX - kLowerBound) % (signed long int)range_size;
}

