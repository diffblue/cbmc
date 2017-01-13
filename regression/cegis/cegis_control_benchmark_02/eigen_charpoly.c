#include <stdio.h>

typedef __CPROVER_fixedbv[24][12] __CPROVER_EIGEN_fixedbvt;

typedef struct {
    //__CPROVER_EIGEN_fixedbvt A[3][3];
    __CPROVER_EIGEN_fixedbvt A[4][4];
    //__CPROVER_EIGEN_fixedbvt B[3][1];
    __CPROVER_EIGEN_fixedbvt B[4][4];
    //__CPROVER_EIGEN_fixedbvt C[1][3];
    __CPROVER_EIGEN_fixedbvt C[4][4];
    //__CPROVER_EIGEN_fixedbvt D[1][1];
    __CPROVER_EIGEN_fixedbvt D[4][4];
    __CPROVER_EIGEN_fixedbvt states[4][4];
    __CPROVER_EIGEN_fixedbvt outputs[4][4];
    __CPROVER_EIGEN_fixedbvt inputs[1][1];
    __CPROVER_EIGEN_fixedbvt K[4][4];
    unsigned int nStates;
    unsigned int nInputs;
    unsigned int nOutputs;
} digital_system_state_space;

__CPROVER_EIGEN_fixedbvt nondet_double(void);

//implementation <7,3>
//states = 3;
//inputs = 1;
//outputs = 1;
//A = [4.6764e-166,0,0;5.1253e-144,0,0;0,2.5627e-144,0]
//B = [0.125;0;0]
//C = [0.16,-5.9787e-32,0]
//D = [0]
//inputs = [1]
#define NSTATES 3u
#define NINPUTS 1u
#define NOUTPUTS 1u

const digital_system_state_space _controller=
{
    .A = { { 4.6764e-166,0.0,0.0,0.0 }, { 5.1253e-144,0.0,0.0,0.0 }, { 0,2.5627e-144,0.0,0.0 } },
    .B = { { 0.125,0.0,0.0,0.0 }, { 0.0,0.0,0.0,0.0 }, { 0.0,0.0,0.0,0.0 } },
    .C = { { 0.16,-5.9787e-32,0.0,0.0 } },
    .D = { { 0.0 } },
    .K = { { nondet_double(), nondet_double(), nondet_double() } },
    .inputs = { { 1.0 } },
    .nStates = NSTATES,
    .nInputs = NINPUTS,
    .nOutputs = NOUTPUTS
};


//typedef int __CPROVER_EIGEN_fixedbvt;
#define __CPROVER_EIGEN_MATRIX_SIZE 3u
#define __CPROVER_EIGEN_POLY_SIZE (__CPROVER_EIGEN_MATRIX_SIZE + 1u)
//const __CPROVER_EIGEN_fixedbvt __CPROVER_EIGEN_TEST_A[__CPROVER_EIGEN_MATRIX_SIZE][__CPROVER_EIGEN_MATRIX_SIZE] = { { 0.0, 1.0, 0.0 }, { 0.0, 0.0, 1.0 }, { 1.0, 0.0, 0.0 } };
extern const __CPROVER_EIGEN_fixedbvt __CPROVER_EIGEN_TEST_A[__CPROVER_EIGEN_MATRIX_SIZE][__CPROVER_EIGEN_MATRIX_SIZE];
__CPROVER_EIGEN_fixedbvt __CPROVER_EIGEN_poly[__CPROVER_EIGEN_POLY_SIZE];

__CPROVER_EIGEN_fixedbvt internal_pow(__CPROVER_EIGEN_fixedbvt a, unsigned int b){
   unsigned int i;
   __CPROVER_EIGEN_fixedbvt acc = 1.0;
   for (i=0; i < b; i++){
    acc = acc*a;
   }
   return acc;
}

__CPROVER_EIGEN_fixedbvt internal_abs(__CPROVER_EIGEN_fixedbvt a){
   return a < 0 ? -a : a;
}

int check_stability(void){
#define __a __CPROVER_EIGEN_poly
#define __n __CPROVER_EIGEN_POLY_SIZE
   int lines = 2 * __n - 1;
   int columns = __n;
   __CPROVER_EIGEN_fixedbvt m[lines][__n];
   int i,j;

   /* to put current values in stability counter-example
    * look for current_stability (use: --no-slice) */
   __CPROVER_EIGEN_fixedbvt current_stability[__n];
   for (i=0; i < __n; i++){
     current_stability[i] = __a[i];
   }

   /* check the first constraint condition F(1) > 0 */
   __CPROVER_EIGEN_fixedbvt sum = 0;
   for (i=0; i < __n; i++){
     sum += __a[i];
   }
   if (sum <= 0){
  printf("[DEBUG] the first constraint of Jury criteria failed: (F(1) > 0)");
     return 0;
   }

   /* check the second constraint condition F(-1)*(-1)^n > 0 */
   sum = 0;
   for (i=0; i < __n; i++){
    sum += __a[i] * internal_pow(-1, __n-1-i);
   }
   sum = sum * internal_pow(-1, __n-1);
   if (sum <= 0){
    printf("[DEBUG] the second constraint of Jury criteria failed: (F(-1)*(-1)^n > 0)");
    return 0;
   }

   /* check the third constraint condition abs(a0 < an*(z^n)  */
   if (internal_abs(__a[__n-1]) > __a[0]){
     printf("[DEBUG] the third constraint of Jury criteria failed: (abs(a0) < a_{n}*z^{n})");
     return 0;
   }

   /* check the fourth constraint of condition (Jury Table) */
   for (i=0; i < lines; i++){
    for (j=0; j < columns; j++){
     m[i][j] = 0;
    }
   }
   for (i=0; i < lines; i++){
    for (j=0; j < columns; j++){
     if (i == 0){
      m[i][j] = __a[j];
      continue;
     }
     if (i % 2 != 0 ){
       int x;
       for(x=0; x<columns;x++){
        m[i][x] = m[i-1][columns-x-1];
       }
       columns = columns - 1;
      j = columns;
     }else{
      m[i][j] = m[i-2][j] - (m[i-2][columns] / m[i-2][0]) * m[i-1][j];
     }
    }
   }
   int first_is_positive =  m[0][0] >= 0 ? 1 : 0;
   for (i=0; i < lines; i++){
    if (i % 2 == 0){
     int line_is_positive = m[i][0] >= 0 ? 1 : 0;
     if (first_is_positive != line_is_positive){
      return 0;
     }
     continue;
    }
   }
   return 1;
}


// P(s)=(s-m11)*(s-m22)*(s-m33) - m13*m31*(s-m22) - m12*m21*(s-m33) - m23*m32*(s-m11) - m12*m23*m31 - m13*m21*m32
// P(s)=s^3 + (-m_11 - m_22 - m_33) * s^2 +  (m_11*m_22 + m_11*m_33 - m_12*m_21 - m_13*m_31 + m_22*m_33 - m_23*m_32) * s - m_11*m_22*m_33 + m_11*m_23*m_32 + m_12*m_21*m_33 - m_12*m_23*m_31 - m_13*m_21*m_32 + m_13*m_22*m_31
void __CPROVER_EIGEN_charpoly(void) {
#define __m __CPROVER_EIGEN_TEST_A
  //                        m_11*m_22*m_33                    + m_11*m_23*m_32                    + m_12*m_21*m_33                    - m_12*m_23*m_31                    - m_13*m_21*m_32                    + m_13*m_22*m_31
  __CPROVER_EIGEN_poly[0] = __m[0][0] * __m[1][1] * __m[2][2] + __m[0][0] * __m[1][2] * __m[2][1] + __m[0][1] * __m[1][0] * __m[2][2] - __m[0][1] * __m[1][2] * __m[2][0] - __m[0][2] * __m[1][0] * __m[2][1] + __m[0][2] * __m[1][1] * __m[2][0];
  //                        (m_11*m_22            + m_11*m_33             - m_12*m_21             - m_13*m_31             + m_22*m_33             - m_23*m_32) * s
  __CPROVER_EIGEN_poly[1] = __m[0][0] * __m[1][1] + __m[0][0] * __m[2][2] - __m[0][1] * __m[1][0] - __m[0][2] * __m[2][0] + __m[1][1] * __m[2][2] - __m[1][2] * __m[2][1];
  //                        (-m_11     - m_22      - m_33) * s^2
  __CPROVER_EIGEN_poly[2] = -__m[0][0] - __m[1][1] - __m[2][2];
  // s^3
  __CPROVER_EIGEN_poly[3] = 1.0;
}

/*void init(void) {
  _controller.K[0][0] = nondet_double();
  _controller.K[0][1] = nondet_double();
  _controller.K[0][2] = nondet_double();
}*/

__CPROVER_EIGEN_fixedbvt __CPROVER_EIGEN_matrix_multiplication_result[4][4];

void double_sub_matrix(void/* unsigned int lines, unsigned int columns, __CPROVER_EIGEN_fixedbvt m1[4][4], __CPROVER_EIGEN_fixedbvt m2[4][4], __CPROVER_EIGEN_fixedbvt result[4][4]*/){
#define __sm_lines NSTATES
#define __sm_columns NSTATES
#define __sm_m1 _controller.A
#define __sm_m2 __CPROVER_EIGEN_matrix_multiplication_result
#define __sm_m3 _controller.A
 unsigned int i, j;
    for (i = 0; i < __sm_lines; i++){
     for (j = 0; j < __sm_columns; j++){
       __sm_m3[i][j] = __sm_m1[i][j] - __sm_m2[i][j];

     }
 }
}

void double_matrix_multiplication(void/* unsigned int i1, unsigned int j1, unsigned int i2, unsigned int j2, __CPROVER_EIGEN_fixedbvt m1[4][4], __CPROVER_EIGEN_fixedbvt m2[4][4], __CPROVER_EIGEN_fixedbvt m3[4][4]*/){
#define __mm_i1 NSTATES
  //unsigned int __mm_i1;
#define __mm_j1 NINPUTS
  //unsigned int __mm_j1;
#define __mm_i2 NINPUTS
  //unsigned int __mm_i2;
#define __mm_j2 NSTATES
  //unsigned int __mm_j2;
#define __mm_m1 _controller.B
  //__CPROVER_EIGEN_fixedbvt __mm_m1[4][4];
#define __mm_m2 _controller.K
  //__CPROVER_EIGEN_fixedbvt __mm_m2[4][4];
#define __mm_m3 __CPROVER_EIGEN_matrix_multiplication_result
  //__CPROVER_EIGEN_fixedbvt __mm_m3[4][4];

 unsigned int i, j, k;
    if (__mm_j1 == __mm_i2) {

        /*for (i=0; i<__mm_i1; i++) {
            for (j=0; j<__mm_j2; j++) {
                __mm_m3[i][j] = 0;
            }
        }*/

        for (i=0;i<__mm_i1; i++) {
            for (j=0; j<__mm_j2; j++) {
                for (k=0; k<__mm_j1; k++) {

                  __CPROVER_EIGEN_fixedbvt mult = (__mm_m1[i][k] * __mm_m2[k][j]);


                    __mm_m3[i][j] = __mm_m3[i][j] + (__mm_m1[i][k] * __mm_m2[k][j]);


                }

            }
        }
    } else {
        printf("\nError! Operation invalid, please enter with valid matrices.\n");
    }
}

#define LIMIT 4u

void closed_loop(void)
{
  //__CPROVER_EIGEN_fixedbvt result1[LIMIT][LIMIT];

  /*int i, j, k;
  for(i=0; i<LIMIT;i++)
  for(j=0; j<LIMIT;j++)
    result1[i][j]=0;*/

  // B*K
  /*double_matrix_multiplication(
  NSTATES,
  NINPUTS,
    NINPUTS,
    NSTATES,
    _controller.B,
    _controller.K,
    result1);*/
  double_matrix_multiplication();

  /*double_sub_matrix(
  _controller.nStates,
  _controller.nStates,
  _controller.A,
  result1,
  _controller.A);*/
  double_sub_matrix();

  /*for(i=0; i<LIMIT;i++)
  for(j=0; j<LIMIT;j++)
    result1[i][j]=0;

  //D*K
  double_matrix_multiplication(
  _controller.nOutputs,
  _controller.nInputs,
    _controller.nInputs,
    _controller.nStates,
    _controller.D,
    _controller.K,
    result1);

  double_sub_matrix(
    _controller.nOutputs,
  _controller.nStates,
  _controller.C,
  result1,
  _controller.C);*/
}

int main(void) {
  //init();
  closed_loop();
  __CPROVER_EIGEN_charpoly();
  //__CPROVER_assert(check_stability(), "");
  __CPROVER_assume(check_stability() == 0);
  __CPROVER_EIGEN_fixedbvt __trace_K0 = _controller.K[0][0];
  __CPROVER_EIGEN_fixedbvt __trace_K1 = _controller.K[0][1];
  __CPROVER_EIGEN_fixedbvt __trace_K2 = _controller.K[0][2];
  __CPROVER_EIGEN_fixedbvt counterexample_var;
  __CPROVER_assume(0.0 <= counterexample_var && counterexample_var <= 10.0);
  __CPROVER_assert(__trace_K0 > counterexample_var, "");
  //__CPROVER_assert(0 == 1, "");
  return 0;
}
