extern "C" void __CPROVER_assert(bool, const char *);
struct __attribute__((packed)) H { unsigned char o : 4; unsigned char k : 4; unsigned short w; };
struct __attribute__((packed)) P { unsigned char o; unsigned short w; };
struct Q { unsigned char o; unsigned short w; } __attribute__((packed));
int main()
{
  __CPROVER_assert(sizeof(P) == 3, "attribute before name: packed honoured");
  __CPROVER_assert(sizeof(Q) == 3, "attribute after body: packed honoured");
  __CPROVER_assert(sizeof(H) == 3, "bitfields + packed before name");
  return 0;
}
