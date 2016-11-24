extern char a[];
char a[255];

// this one is funny
unsigned char rtc_cmos_read(unsigned char addr)
{
}

extern __typeof__(rtc_cmos_read) rtc_cmos_read;

int main()
{
  return 0;
}
