typedef unsigned bool;

#define true 1
#define false 0

typedef char Register;

enum RegisterId
{
  SIGNAL_REG_ID = 0,
  DATA_A_REG_ID = 1,

  REG_NR = 2
};

typedef enum RegisterId RegisterId;

struct Firmware;
typedef void (*InterruptHandler)(struct Firmware *fw, RegisterId reg_id);

struct Hardware
{
  struct Firmware* fw;

  Register regs[REG_NR];
  bool is_on;

  InterruptHandler interrupt_handler;
};

Register read_data_register(struct Hardware *hw, RegisterId reg_id)
{
  if (!hw->is_on)
    return '\0';

  Register reg = hw->regs[reg_id];
  hw->regs[SIGNAL_REG_ID] &= ~reg_id;

  return reg;
}

void write_data_register(struct Hardware *hw, RegisterId reg_id, Register data)
{
  check_data_register(reg_id);

  if (!hw->is_on)
    return;

  hw->regs[reg_id] = data;
  hw->regs[SIGNAL_REG_ID] |= reg_id;

  __CPROVER_ASYNC_1: hw->interrupt_handler(hw->fw, reg_id);
}

struct Firmware
{
  struct Hardware* hw;
};

void handle_interrupt(struct Firmware *fw, RegisterId reg_id)
{
  assert(reg_id == DATA_A_REG_ID);
  read_data_register(fw->hw, DATA_A_REG_ID);
}

void poll(struct Firmware *fw)
{
  char byte;
  if (byte == '\0')
  {
    enable_interrupts(fw->hw, handle_interrupt);
    return;
  }
}

void write_reg_a(struct Hardware *hw)
{
  write_data_register(hw, DATA_A_REG_ID, nondet_char());
}

int main(void)
{
  // trivial bug
  assert(false);

  struct Hardware hardware;
  struct Hardware* hw = &hardware;

  struct Firmware firmware;
  struct Firmware* fw = &firmware;

  firmware.hw = hw;
  hardware.fw = fw;

  __CPROVER_ASYNC_1: write_reg_a(hw);

  return 0;
}
