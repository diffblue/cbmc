#include <assert.h>
#include <stdio.h>

unsigned int control = 0;
unsigned int history = 0;

unsigned int choose (void) {
  unsigned int lsb = control & 0x1u;
  control = control >> 1;
  history = (history << 1) | lsb;
  return lsb;
}

void red (void) {
  printf("Red\n");
}
void blue (void) {
  printf("Blue\n");
}

void test (void) {
  while (choose()) {
    if (choose()) {
      red();  // Is this in the loop?
      break;
      
    } else if (choose()) {
      goto out;
    }
  }

  if (0) {
  out: blue();  // What about this?
  }

  return;
}


int main (int argc, char **argv) {
  scanf("%u", &control);
    
  test();

  printf("%u\n", history);
  // History is (100)*(0|11|101)

  // Let's check that
  if (history == 0u) {
    // Fine
  } else {
    if ((history & 0x7) == 0x5) {
      history = history >> 3;
    } else if ((history & 0x3) == 0x3) {
      history = history >> 2;
    } else if ((history & 0x1) == 0x0) {
      history = history >> 1;
    } else {
      assert(0);
    }

    while ((history & 0x7) == 0x4) {
      history = history >> 3;
    }

    assert(history == 0);
  }
  
  return 0;
}
