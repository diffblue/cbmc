class c {
public :
  c& operator ++(void) { return *this; }
};

int main (void) {
  c p;

  p = ++p;

  return 1;
}
