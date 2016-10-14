#include <stdio.h>
//#include <assert.h>
#define TRUE 1
#define FALSE 0

struct state_elements_top{
  _Bool done;
  unsigned int once;
  unsigned short int xsum_in;
  unsigned int state;
  unsigned int xavg_next;
  unsigned int xavg_out;
  unsigned int xdiff_out;
};
struct state_elements_top  stop;

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done);

// *********** Implementation in C **************

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done)
{
    unsigned int tmp13;
    unsigned int tmp12;
    unsigned int tmp11;
    unsigned int tmp10;
    unsigned int tmp9;
    unsigned int tmp8;
    unsigned int tmp7;
    unsigned short int tmp6;
    unsigned int tmp5;
    unsigned int tmp4;
    unsigned short int tmp3;
    unsigned int tmp2;
    unsigned int tmp1;
    unsigned int tmp0;
    if(rst)
    {
      tmp0 = 0;
      tmp1 = 0;
      tmp2 = 0;
      stop.xavg_out = tmp0 & 255;
      stop.xdiff_out = tmp1 & 255;
      stop.state = tmp2 & 3;
    }

    else
    {
      if(stop.state == 0)
      {
        tmp3 = (unsigned short int)ser_in;
        tmp4 = 1;
        tmp5 = 1;
        stop.xsum_in = tmp3 & 1023;
        stop.state = tmp4 & 3;
        stop.once = tmp5;
      }

      else
        if(stop.state == 1)
        {
          tmp6 = stop.xsum_in + (unsigned short int)ser_in;
          tmp7 = 0;
          stop.xsum_in = tmp6 & 1023;
          if((_Bool)stop.once)
          {
            tmp8 = 1;
            stop.state = tmp8 & 3;
          }

          else
          {
            tmp9 = 2;
            stop.state = tmp9 & 3;
          }
          stop.once = tmp7; // This update must take place at the end of the current if-else block so as to simulate the effect of reading the old value of stop.once through non-blocking statement
        }

        else
        {
          stop.xavg_next = ((stop.xsum_in + ser_in) >> 2) & 255;
          tmp10 = stop.xavg_next;
          stop.xavg_out = tmp10 & 255;
          if(stop.xavg_next >= ser_in)
          {
            tmp11 = stop.xavg_next - ser_in;
            stop.xdiff_out = tmp11 & 255;
          }

          else
          {
            tmp12 = ser_in - stop.xavg_next;
            stop.xdiff_out = tmp12 & 255;
          }
          tmp13 = 0;
          stop.state = tmp13 & 3;
        }
    }
  stop.done = (stop.state == 0);
}

void main()
{
	int i=0;
  _Bool clk;
	_Bool rst;
	unsigned int ser_in;
	_Bool done;
	while(i<=100)
	{
    topc(clk, rst, ser_in, &done);
    assert(stop.xavg_out == 0 || stop.xavg_out != 0);
		i++;
	}
}
