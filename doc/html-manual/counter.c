void next_timeframe();

struct module_top {
  unsigned int counter;
};

extern const struct module_top top;

int main() {
  next_timeframe();
  next_timeframe();
  assert(top.counter==2);
  next_timeframe();
  assert(top.counter==3);
}
