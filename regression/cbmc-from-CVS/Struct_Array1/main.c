int main() {
  struct a {
    int f;
  } x[1];
  
  struct a y;

  x[0].f = 7;

  assert(x[0].f == 7);

  y = x[0];

  assert(y.f == 7);
}
