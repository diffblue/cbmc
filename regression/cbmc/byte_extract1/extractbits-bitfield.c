// Regression test for issue #8581
// When unpacking a non-byte-aligned bitfield into bytes, extractbits
// operations were created that exceeded the source bitvector width.
typedef a;
union
{
  signed : 28;
  signed : 25;
  a *b;
} c = {10};
main()
{
  d();
}
