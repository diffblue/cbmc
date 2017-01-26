
#define N 4
const int g_N = N;

int nobody_func(int a);

int g_a[N];

void func(int a) {
  int i;
  int n = g_N;
  for (i=0; i < n; i++)  //   expected 4
     g_a[i] = nobody_func(a);
}

void main(void)
{
  func(1);
  func(1);  // multi
}

