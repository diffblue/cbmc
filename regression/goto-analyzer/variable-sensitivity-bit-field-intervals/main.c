struct bitfield_struct
{
  unsigned char byte;
  unsigned char bitfield : 1;
};

extern struct bitfield_struct bs;

void main(void)
{
  bs.byte = 10;
  bs.bitfield = 1;
  __CPROVER_assert(bs.byte == 10, "bs.byte==10");
  __CPROVER_assert(bs.bitfield == 1, "bs.bitfield==1");
}
