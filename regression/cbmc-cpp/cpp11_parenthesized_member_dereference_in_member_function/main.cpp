extern "C" void __CPROVER_assert(bool, const char *);
unsigned long word = 5;
struct reference
{
  unsigned long *wp;
  unsigned pos;
  // libstdc++'s bitset::reference::operator~ / operator bool:
  // `(*(_M_wp) & _Base::_S_maskbit(_M_bpos)) == 0'
  bool get() const
  {
    return (*(wp) & (1ul << pos)) != 0;
  }
  bool flipped() const
  {
    return (*(wp) & (1ul << pos)) == 0;
  }
};
int main()
{
  reference r{&word, 2};
  __CPROVER_assert(r.get(), "bit 2 is set");
  __CPROVER_assert(!r.flipped(), "its complement is clear");
  reference s{&word, 1};
  __CPROVER_assert(!s.get(), "bit 1 is clear");
  __CPROVER_assert(s.get(), "WRONG (must FAIL)");
}
