union u {
  int x;
  float f;

  u(): x(42) { }
  u(int): f(1.0) { }
  union u &operator=(union u) { return *this; }

  ~u()
  {
  }
};

int main (void) {
  u _u;

  return 0;
}
