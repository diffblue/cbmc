#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

#define MAX 1000
#define SIZE 10

unsigned int sample()
{
  return random()%(MAX+1);
}

unsigned int ring_buffer[SIZE];

int main()
{
  unsigned index=0, previous_index=SIZE-1;

  while(1)
  {
    unsigned output;
    output=(ring_buffer[index]+ring_buffer[previous_index])/2;
    assert(ring_buffer[index]<=MAX);
    assert(output<=MAX);

    ring_buffer[index]=sample();

    previous_index=index;
    index=(index+1)%SIZE;

    assert(index<SIZE);
  }
}
