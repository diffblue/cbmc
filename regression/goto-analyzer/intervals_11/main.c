
const int xLen = 10;
const int Alen = 2;
const int Blen = 1;
float nondet_float();
int main() {
  float A[] = {1.0f,-0.5f};
  float B[] = {1.0f};
  int i,j;
  float x[xLen];
  float x_aux[xLen];
  float y[xLen];
  float y_aux[xLen];
  float total=0;
  for (i=0;i<xLen;i++) {
    x[i] = nondet_float();
    __CPROVER_assume(x[i]>=-1 && x[i]<=1);
    x_aux[i]=0;
    y_aux[i]=0;
  }
  for(i=0;i<xLen;i++) {
    y[i] = 0; //clear y
    /* Update past x values */
    for(j=Blen-1;j>=1;j--)
      x_aux[j] = x_aux[j-1];
    x_aux[0] = x[i];
    /* Num, x values */
    for (j = 0; j < Blen; j++) {
      y[i] = y[i] + B[j]*x_aux[j];
      __CPROVER_assert(
        y[i] >= -1.0f && y[i] <= 1.0f, "y[i]>=-1.0f && y[i]<=1.0f"); //success
    }
    /* Den, y values */
    for(j=0;j<Alen-1;j++) {
      y[i] = y[i]-A[j+1]*y_aux[j];
      __CPROVER_assert(
        y[i] >= -1.0f && y[i] <= 1.0f, "y[i]>=-1.0f && y[i]<=1.0f"); //fails
    }
    /* Update past y values */
    for(j=Alen-2;j>=1;j--)
      y_aux[j] = y_aux[j-1];
    y_aux[0] = y[i];
  }
}

