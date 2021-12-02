// Benchmark built by Alex Horn
// This small ANSI C file can be compiled with various options.
// For example, "CC -D_EXPOSE_BUG_ generic_hw_sw_benchmark.c"
// produces an executable file that when run exposes the
// concurrency bug in the hardware/software interface.

// ========= Build specifics =========

#ifdef _ENABLE_CBMC_

#  define ASYNC(n, c) __CPROVER_ASYNC_##n : (c)
#  define ATOMIC_BEGIN __CPROVER_atomic_begin()
#  define ATOMIC_END __CPROVER_atomic_end()

char symbolic_char(char);

#else

#include <assert.h>
#undef ASYNC

char symbolic_char(char c)
{
  return c;
}

#endif

#ifdef _ENABLE_POSIX_

#include <pthread.h>

#define ATOMIC_BEGIN pthread_mutex_lock(&hw->lock)
#define ATOMIC_END pthread_mutex_unlock(&hw->lock)

#endif

// There are three ways to expose the concurrency bug:
// 1) delay enabling of interrupt so that an intermittent
//    stimulus won't trigger an interrupt;
// 2) delay the firing of the interrupt handler until
//    after the verification condition check;
// 3) generate stimulus before polling starts.
#ifdef _EXPOSE_BUG_
#include <unistd.h>

#define SHORT_DELAY 1
#define LONG_DELAY 3
#endif

// Marginally useful in case of concurrent outputs
#ifdef _ENABLE_OUTPUT_
#include <stdio.h>
#endif

// ========= C conveniences =========

typedef unsigned bool;

#define true 1
#define false 0

#if !defined(_ENABLE_POSIX_) && !defined(NULL)
#define NULL 0
#endif

// ========= Hardware model =========

typedef char Register;
#define ZERO_BYTE '\0'

enum RegisterId
{
  SIGNAL_REG_ID = 0,
  DATA_A_REG_ID = 1,

  REG_NR = 2
};

typedef enum RegisterId RegisterId;
typedef void* (*InterruptHandler)(void*);

struct Hardware
{
  struct Firmware* fw;

#ifdef _ENABLE_POSIX_
  pthread_mutex_t lock;
#endif

  Register regs[REG_NR];
  bool is_on;

  // Fire interrupt whenever handler is not null
  InterruptHandler interrupt_handler;
};

// By default interrupts are disabled
void turn_on(struct Hardware *hw)
{
  ATOMIC_BEGIN;

#ifdef _ENABLE_POSIX_
  pthread_mutex_init(&hw->lock, NULL);
#endif

#ifdef _ENABLE_OUTPUT_
  printf("Turn on hardware\n");
#endif

  for (unsigned reg_id = 0; reg_id < REG_NR; ++reg_id)
    hw->regs[reg_id] = ZERO_BYTE;

  hw->is_on = true;
  hw->interrupt_handler = NULL;

  ATOMIC_END;
}

void turn_off(struct Hardware *hw)
{
  ATOMIC_BEGIN;

#ifdef _ENABLE_OUTPUT_
  printf("Turn off hardware\n");
#endif

  hw->is_on = false;

  ATOMIC_END;
}

// Does not write any registers but sets function pointer
void enable_interrupts(struct Hardware *hw, InterruptHandler interrupt_handler)
{
  ATOMIC_BEGIN;

  hw->interrupt_handler = interrupt_handler;

  ATOMIC_END;
}

// Read control register
Register read_signal_register(struct Hardware *hw)
{
  ATOMIC_BEGIN;

  Register reg = ZERO_BYTE;
  if (!hw->is_on)
  {
#ifdef _ENABLE_OUTPUT_
    printf("Read signal [off]\n");
#endif
    goto SKIP;
  }

  reg = hw->regs[SIGNAL_REG_ID];

SKIP:
  ATOMIC_END;
  return reg;
}

// Internal check that `reg_id' refers to a data register
void check_data_register(RegisterId reg_id)
{
  assert(0 < reg_id && reg_id < REG_NR);
}

// Read data from hardware register
Register read_data_register(struct Hardware *hw, RegisterId reg_id)
{
  ATOMIC_BEGIN;
  check_data_register(reg_id);

  Register value = ZERO_BYTE;

  if (!hw->is_on)
  {
#ifdef _ENABLE_OUTPUT_
    printf("Read register [off] %d\n", reg_id);
#endif
    goto SKIP;
  }

  value = hw->regs[reg_id];
  hw->regs[SIGNAL_REG_ID] &= ~reg_id;

#ifdef _ENABLE_OUTPUT_
  printf("Read register [on] reg_id: %d value: %c\n", reg_id, value);
#endif

SKIP:
  ATOMIC_END;
  return value;
}

// Write data to hardware register
void* write_data_register(struct Hardware *hw, RegisterId reg_id, Register value)
{
  ATOMIC_BEGIN;
  check_data_register(reg_id);

  if (!hw->is_on)
  {
#ifdef _ENABLE_OUTPUT_
    printf("Write register [off] reg_id: %d value: %c\n", reg_id, value);
#endif
    goto SKIP;
  }

#ifdef _ENABLE_OUTPUT_
  printf("Write register [on] reg_id: %d value: %c\n", reg_id, value);
#endif

  hw->regs[reg_id] = value;
  hw->regs[SIGNAL_REG_ID] |= reg_id;

  if (hw->interrupt_handler)
#ifdef _ENABLE_POSIX_
  {
#ifdef _ENABLE_OUTPUT_
    printf("Fire interrupt\n");
#endif

#ifdef _EXPOSE_BUG_
    // delay firing of interrupt
    sleep(LONG_DELAY);
#endif

    // caution: detached thread!
    pthread_t interrupt_thread;
    pthread_create(&interrupt_thread, NULL, hw->interrupt_handler, (void *) hw->fw);
  }
#else
    ASYNC(1, hw->interrupt_handler((void *)hw->fw));
#endif

SKIP:
  ATOMIC_END;
  return NULL;
}

// ========= Firmware =========

// Reads the data registers
//
// Switches to interrupt mode if there
// is no data to read.
struct Firmware
{
  struct Hardware* hw;
};

// Interrupt handler for incoming data
void* handle_interrupt(void *ptr)
{
#ifdef _ENABLE_OUTPUT_
  printf("Handle interrupt\n");
#endif

  struct Firmware *fw = (struct Firmware*) ptr;
  read_data_register(fw->hw, DATA_A_REG_ID);

#ifdef _ENABLE_POSIX_
  pthread_exit(0);
#endif

  return NULL;
}

// Firmware's main function

// Switches from polling to interrupt mode if
// there is no newly written data to read.
void* poll(void *ptr)
{
  struct Firmware *fw = (struct Firmware*) ptr;
  char byte = read_signal_register(fw->hw);

  if (byte == ZERO_BYTE)
  {
#ifdef _ENABLE_OUTPUT_
    printf("Switch from polling to interrupt mode\n");
#endif

    enable_interrupts(fw->hw, handle_interrupt);
  }
  else
  {
#ifdef _ENABLE_OUTPUT_
    printf("Stay in polling mode and read hardware register\n");
#endif

    read_data_register(fw->hw, DATA_A_REG_ID);
  }

#ifdef _ENABLE_POSIX_
  pthread_exit(0);
#endif

  return NULL;
}

// ========= Test harness =========

void* stimulus(void *ptr)
{
  struct Hardware *hw = (struct Hardware*) ptr;
  Register value = symbolic_char('A');

#ifdef _ENABLE_OUTPUT_
  printf("Generate stimulus\n");
#endif

  write_data_register(hw, DATA_A_REG_ID, value);

#ifdef _ENABLE_POSIX_
  pthread_exit(0);
#endif

  return NULL;
}

int main(void)
{
#ifdef _ENABLE_OUTPUT_
  printf("C main(void) function\n");
#endif

  struct Hardware hardware;
  struct Hardware* hw = &hardware;

  struct Firmware firmware;
  struct Firmware* fw = &firmware;

  // burn firmware on chip
  firmware.hw = hw;
  hardware.fw = fw;

  // start hardware
  turn_on(hw);

  // start firmware
#ifdef _ENABLE_POSIX_
  pthread_t firmware_thread;
  pthread_create(&firmware_thread, NULL, poll, (void *) fw);
#else
  ASYNC(1, poll((void *)fw));
#endif

#ifdef _EXPOSE_BUG_
  sleep(SHORT_DELAY);
#endif

  // environment stimulus
#ifdef _ENABLE_POSIX_
  pthread_t stimulus_thread;
  pthread_create(&stimulus_thread, NULL, stimulus, (void *) hw);
#else
  ASYNC(2, stimulus((void *)hw));
#endif

#ifdef _EXPOSE_BUG_
  sleep(SHORT_DELAY);
#endif

  // stop hardware
  turn_off(hw);

  // check verification condition:
  //
  // the firmware must have reacted to every environment
  // stimulus that triggered the hardware functionality.
  assert(hardware.regs[SIGNAL_REG_ID] == 0);

#ifdef _ENABLE_POSIX_
  pthread_join(firmware_thread, NULL);
  pthread_join(stimulus_thread, NULL);
  pthread_mutex_destroy(&hw->lock);
#endif

  return 0;
}
