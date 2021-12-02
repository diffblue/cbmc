// c::tag-IRQState
// file ../../../qemu-hw/ethoc/irq.h line 28
struct IRQState;

// c::tag-Mii
// file ../../../qemu-hw/ethoc/opencores_eth.h line 49
struct Mii;

// c::tag-NICState
// file ../../../qemu-hw/ethoc/net.h line 32
struct NICState;

// c::tag-NetClientInfo
// file ../../../qemu-hw/ethoc/net.h line 17
struct NetClientInfo;

// c::tag-NetClientState
// file ../../../qemu-hw/ethoc/net.h line 24
struct NetClientState;

// c::tag-OpenEthState
// file ../../../qemu-hw/ethoc/opencores_eth.h line 318
struct OpenEthState;

// c::tag-device
// file device.h line 18
struct device;

// c::tag-ethoc
// file ethoc.c line 193
struct ethoc;

// c::tag-list_head
// file list.h line 6
struct list_head;

// c::tag-napi_struct
// file napi.h line 11
struct napi_struct;

// c::tag-net_device
// file netdevice.h line 82
struct net_device;

// c::tag-net_device_stats
// file netdevice.h line 39
struct net_device_stats;

// c::tag-netdev_hw_addr_list
// file netdevice.h line 67
struct netdev_hw_addr_list;

// c::tag-open_eth_desc
// file ../../../qemu-hw/ethoc/opencores_eth.h line 309
struct open_eth_desc;

#include <assert.h>

struct IRQState
{
  // handler
  int (*handler)(void *opaque, signed int n, signed int level);
  // opaque
  void *opaque;
  // n
  signed int n;
};

struct Mii
{
  // regs
  unsigned short int regs[6];
  // link_ok
  _Bool link_ok;
};

struct NetClientState
{
  // info
  struct NetClientInfo *info;
  // link_down
  signed int link_down;
  // peer
  struct NetClientState *peer;
  // receive_disabled
  unsigned int receive_disabled;
};

struct NICState
{
  // nc
  struct NetClientState nc;
  // opaque
  void *opaque;
};

struct NetClientInfo
{
  // can_receive
  signed int (*can_receive)(struct NetClientState *);
  // receive
  signed int (*receive)(struct NetClientState *, const unsigned char *, unsigned int);
  // link_status_changed
  void (*link_status_changed)(struct NetClientState *);
};

struct open_eth_desc
{
  // len_flags
  unsigned int len_flags;
  // buf_ptr
  unsigned int buf_ptr;
};

struct OpenEthState
{
  // nic
  struct NICState *nic;
  // irq
  struct IRQState *irq;
  // mii
  struct Mii mii;
  // regs
  unsigned int regs[21];
  // tx_desc
  unsigned int tx_desc;
  // rx_desc
  unsigned int rx_desc;
  // desc
  struct open_eth_desc desc[8];
  // software
  void *software;
};

struct device
{
};

struct napi_struct
{
  // complete
  signed int complete;
  // weight
  signed int weight;
  // sched
  signed int sched;
  // is_disabling
  signed int is_disabling;
  // poll
  signed int (*poll)(struct napi_struct *, signed int);
};

struct ethoc
{
  // num_tx
  unsigned int num_tx;
  // cur_tx
  unsigned int cur_tx;
  // dty_tx
  unsigned int dty_tx;
  // num_rx
  unsigned int num_rx;
  // cur_rx
  unsigned int cur_rx;
  // dma_buf
  void *dma_buf;
  // dma_regions
  void **dma_regions;
  // netdev
  struct net_device *netdev;
  // napi
  struct napi_struct napi;
  // phy_id
  signed char phy_id;
  // open_eth
  struct OpenEthState *open_eth;
};

struct list_head
{
  // next
  struct list_head *next;
  // prev
  struct list_head *prev;
};

struct netdev_hw_addr_list
{
  // list
  struct list_head list;
  // count
  signed int count;
};

struct net_device_stats
{
  // rx_packets
  unsigned long int rx_packets;
  // tx_packets
  unsigned long int tx_packets;
  // rx_bytes
  unsigned long int rx_bytes;
  // tx_bytes
  unsigned long int tx_bytes;
  // rx_errors
  unsigned long int rx_errors;
  // tx_errors
  unsigned long int tx_errors;
  // rx_dropped
  unsigned long int rx_dropped;
  // tx_dropped
  unsigned long int tx_dropped;
  // multicast
  unsigned long int multicast;
  // collisions
  unsigned long int collisions;
  // rx_length_errors
  unsigned long int rx_length_errors;
  // rx_over_errors
  unsigned long int rx_over_errors;
  // rx_crc_errors
  unsigned long int rx_crc_errors;
  // rx_frame_errors
  unsigned long int rx_frame_errors;
  // rx_fifo_errors
  unsigned long int rx_fifo_errors;
  // rx_missed_errors
  unsigned long int rx_missed_errors;
  // tx_aborted_errors
  unsigned long int tx_aborted_errors;
  // tx_carrier_errors
  unsigned long int tx_carrier_errors;
  // tx_fifo_errors
  unsigned long int tx_fifo_errors;
  // tx_heartbeat_errors
  unsigned long int tx_heartbeat_errors;
  // tx_window_errors
  unsigned long int tx_window_errors;
  // rx_compressed
  unsigned long int rx_compressed;
  // tx_compressed
  unsigned long int tx_compressed;
};

struct net_device
{
  // mc
  struct netdev_hw_addr_list mc;
  // mem_end
  unsigned long int mem_end;
  // mem_start
  unsigned long int mem_start;
  // flags
  unsigned int flags;
  // stats
  struct net_device_stats stats;
  // dev
  struct device dev;
  // priv
  void *priv;
};

// c::netdev_priv
// file netdevice.h line 133
static void * netdev_priv(struct net_device *dev)
{
  return dev->priv;
}

// c::open_eth_reg_write
// file ../../../qemu-hw/ethoc/opencores_eth.c line 516
void open_eth_reg_write(struct OpenEthState *s, unsigned int addr, unsigned int val)
{
  s->regs[0 + 1 + 1] = val;
}

// c::ethoc_reset
// file ethoc.c line 364
static signed int ethoc_reset(struct ethoc *dev)
{
  unsigned int mode;

__CPROVER_ASYNC_1:
  open_eth_reg_write(dev->open_eth, (unsigned int)0, mode);

__CPROVER_ASYNC_2:
  open_eth_reg_write(dev->open_eth, (unsigned int)0, mode);
  return 0;
}

// c::ethoc_open
// file ethoc.c line 718
static signed int ethoc_open(struct net_device *dev)
{
  struct ethoc *priv;
  void *return_value_netdev_priv$1;
  return_value_netdev_priv$1=netdev_priv(dev);
  priv = (struct ethoc *)return_value_netdev_priv$1;
  ethoc_reset(priv);
  return 0;
}

// c::main
// file ethoc.c line 894
signed int main(void)
{
  struct net_device netdev;
  assert((_Bool)0);
  ethoc_open(&netdev);
  return 0;
}
