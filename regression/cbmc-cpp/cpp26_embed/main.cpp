// N5008 [cpp.embed]: #embed ([cpp.embed]) of a 3-byte file: the preprocessor
// produces the bytes as a comma-separated list, so CBMC sees an ordinary
// initializer. Needs a preprocessor implementing #embed (GCC 15 or later;
// tagged libstdcxx16 as that tag checks the host gcc's version)..
extern "C" void __CPROVER_assert(bool, const char *);
const unsigned char data[] = {
#embed "data.bin"
};
int main()
{
  __CPROVER_assert(
    sizeof(data) == 3 && data[0] == 0x41 && data[2] == 0x43, "embedded bytes");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
