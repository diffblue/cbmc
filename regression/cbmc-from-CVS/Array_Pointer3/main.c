int x, y;

int z[10];

void h(int w) {
  x = x + 1;
  y = y + 1;
}

_Bool strict_sorted(int a[], int len, int s) {
  int i;
  for (i = s; i < len-1; i++) {
    if (a[i] >= a[i+1])
      return 0;
  }
  return 1;
}

_Bool sorted(int a[], int len, int s) {
  int i;
  for (i = s; i < len-1; i++) {
    if (a[i] > a[i+1])
      return 0;
  }
  return 1;
}

int g (int w) {
  int i;
  int local_arr[50];
  assert(w >= 1);
  x = w;
  w--;
  y = w;
  for(i = 0; i < 10; i++)
    z[i] = i;
  assert(strict_sorted(z,10,0));
  assert(x > y);
}

int f (int j, int k) {
  int i;
  assert(j > k);
  assert(j >= 0);
  assert((k > 10) && (k < 20));
  j -= k;
  g(j);
  j = k;
  y = k;
  g(j);
  h(j);
  assert(sorted(z,10,5));
  assert(x >= y);
}

int main () {
  int x, y;
  __CPROVER_assume (x > y);
  __CPROVER_assume (x >= 0);
  __CPROVER_assume ((y > 15) && (y < 18));
  f(x,y);
}
