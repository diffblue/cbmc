class c {
public :
  friend c operator ~(c p);
};

c operator ~(c p) { return p; }


int main (void) {
  c p;

  p = ~p;

  return 1;
}
