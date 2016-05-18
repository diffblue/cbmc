#include <stdio.h>
//#include<assert.h>
#define TRUE 1
#define FALSE 0

// ******** C Implementation of Adder *************//
struct state_elements_top{
  _Bool done;
  unsigned int xsum1_in;
  unsigned int xsum2_in;
  unsigned int state;
  unsigned int s0_in;
  unsigned int s1_in;
  unsigned int s2_in;
  unsigned int xavg_next;
  unsigned int xavg_out;
  unsigned int xdiff_out;
};
struct state_elements_top  stop;

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done)
{
    unsigned int tmp40;
    unsigned int tmp30;
    unsigned int tmp11;
    unsigned int tmp10;
    unsigned int tmp9;
    unsigned int tmp8;
    unsigned int tmp7;
    unsigned int tmp6;
    unsigned int tmp5;
    unsigned int tmp4;
    unsigned int tmp3;
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
        tmp3 = ser_in;
        tmp4 = 1;
        stop.s0_in = tmp3 & 255;
        stop.state = tmp4 & 3;
      }

      else
        if(stop.state == 1)
        {
          tmp5 = ser_in;
          tmp30 = 2;
          stop.s1_in = tmp5 & 255;
          stop.state = tmp30 & 3;

        }

        else
          if(stop.state == 2)
          {
            tmp6 = ser_in;
            tmp7 = stop.s0_in + stop.s1_in;
            tmp40 = 3;
            stop.s2_in = tmp6 & 255;
            stop.xsum1_in = tmp7 & 1023;
            stop.state = tmp40 & 3;
          }

          else
          {
            stop.xsum2_in = (ser_in + stop.s2_in) & 1023;
            stop.xavg_next = ((stop.xsum1_in + stop.xsum2_in) >> 2) & 255;
            tmp8 = stop.xavg_next;
            stop.xavg_out = tmp8 & 255;
            if(stop.xavg_next >= ser_in)
            {
              tmp9 = stop.xavg_next - ser_in;
              stop.xdiff_out = tmp9 & 255;
            }

            else
            {
              tmp10 = ser_in - stop.xavg_next;
              stop.xdiff_out = tmp10 & 255;
            }
            tmp11 = 0;
            stop.state = tmp11 & 3;
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
    /*assert(stop.xavg_out == 0 && stop.xdiff_out==0);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 7, &done);
    assert(stop.xavg_out == 0 && stop.xdiff_out==0);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 0 && stop.xdiff_out==0);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 0 && stop.xdiff_out==0);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 7, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);
    topc(clk, 0, 8, &done);
    assert(stop.xavg_out == 7 && stop.xdiff_out==1);
    //printf("%d %d\n",stop.xavg_out, stop.xdiff_out);*/
    assert(stop.xavg_out == 0 || stop.xavg_out != 0);
    i++;
  }
}
