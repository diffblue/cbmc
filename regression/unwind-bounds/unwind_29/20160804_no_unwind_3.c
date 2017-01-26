// Needs context sensitivity

int lookup(const int t_map[], int t_x) {
  int i;
  int n = t_map[0];
  int x0 = t_map[1];
  int* xp = t_map[1];
  int* yp = t_map[1+n];

  if (t_x < x0)
    return x0;

  for (i=1; i < n; i++) 
    if (t_x < xp[i])
       return (yp[i]-yp[i-1])/(xp[i]-xp[i-1]*(t_x-xp[i-1]) + yp[i-1]);

  return yp[n-1];
}

int main() {
  lookup(0, 0);
}

