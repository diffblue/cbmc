#define _cbmc_printf2(str, var)                                                \
  {                                                                            \
    unsigned int ValueOf_##str = (unsigned int)var;                            \
  }

#define BUFFER_SIZE 100
typedef struct
{
  int buffer[BUFFER_SIZE];
} buffert;

#define BUF_BASE 0x1000
#define BUF0_BASE (BUF_BASE + 0x00000)
#define BUF1_BASE (BUF_BASE + 0x10000)
#define BUF2_BASE (BUF_BASE + 0x20000)
#define BUF3_BASE (BUF_BASE + 0x30000)

#define BUF0 ((buffert *)BUF0_BASE)
#define BUF1 ((buffert *)BUF1_BASE)
#define BUF2 ((buffert *)BUF2_BASE)
#define BUF3 ((buffert *)BUF3_BASE)

static buffert(*const buffers[4]) = {BUF0, BUF1, BUF2, BUF3};

main()
{
  __CPROVER_allocated_memory(BUF0_BASE, sizeof(buffert));
  __CPROVER_allocated_memory(BUF1_BASE, sizeof(buffert));
  __CPROVER_allocated_memory(BUF2_BASE, sizeof(buffert));
  __CPROVER_allocated_memory(BUF3_BASE, sizeof(buffert));

  _cbmc_printf2(sizeof_buffers, sizeof(buffers));
  _cbmc_printf2(sizeof_buffers_0, sizeof(buffers[0]));
  _cbmc_printf2(sizeof_buffer, sizeof(buffers[0]->buffer));

  buffers[0]->buffer[0];
  buffers[0]->buffer[BUFFER_SIZE - 1];
  buffers[0]->buffer[BUFFER_SIZE]; // should be out-of-bounds
}
