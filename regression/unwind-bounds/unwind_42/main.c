
void nobody_func(void);

int g_var_n;
const int g_const_n = 4;
#define N  4
int g_var_array[N];

void main(void)
{
  int i;
  int n = N;

  ///// maybe effect global vars 
  nobody_func();

  // 0: local var after function-call   (expected 4)
  for (i=0; i < n; i++)
     g_var_array[i] ++;

  // 1: global const var after function-call  (expected 4)
  for (i=0; i < g_const_n; i++)
     g_var_array[i] ++;

  // 2: global var after function-call   (expected -1)
  for (i=0; i < g_var_n; i++)
     g_var_array[i] ++;
} 

