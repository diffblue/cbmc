#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

enum {
 RTAX_UNSPEC,
 RTAX_LOCK,
 RTAX_MTU,
 RTAX_WINDOW,
 RTAX_RTT,
 RTAX_RTTVAR,
 RTAX_SSTHRESH,
 RTAX_CWND,
 RTAX_ADVMSS,
 RTAX_REORDERING,
 RTAX_HOPLIMIT,
 RTAX_INITCWND,
 RTAX_FEATURES,
 RTAX_RTO_MIN,
 RTAX_INITRWND,
 __RTAX_MAX
};

typedef __signed__ char __s8;
typedef unsigned char __u8;

typedef __signed__ short __s16;
typedef unsigned short __u16;

typedef __signed__ int __s32;
typedef unsigned int __u32;

__extension__ typedef __signed__ long long __s64;
__extension__ typedef unsigned long long __u64;
typedef signed char s8;
typedef unsigned char u8;

typedef signed short s16;
typedef unsigned short u16;

typedef signed int s32;
typedef unsigned int u32;

typedef signed long long s64;
typedef unsigned long long u64;

typedef unsigned char u_char;
typedef unsigned short u_short;
typedef unsigned int u_int;
typedef unsigned long u_long;

typedef unsigned char unchar;
typedef unsigned short ushort;
typedef unsigned int uint;
typedef unsigned long ulong;

typedef __u8 u_int8_t;
typedef __s8 int8_t;
typedef __u16 u_int16_t;
typedef __s16 int16_t;
typedef __u32 u_int32_t;
typedef __s32 int32_t;

typedef __u8 uint8_t;
typedef __u16 uint16_t;
typedef __u32 uint32_t;

typedef __u64 uint64_t;
typedef __u64 u_int64_t;
typedef __s64 int64_t;
typedef unsigned long sector_t;
typedef unsigned long blkcnt_t;
typedef __u16 __le16;
typedef __u16 __be16;
typedef __u32 __le32;
typedef __u32 __be32;
typedef __u64 __le64;
typedef __u64 __be64;

typedef __u16 __sum16;
typedef __u32 __wsum;


typedef unsigned gfp_t;
typedef unsigned fmode_t;


typedef u64 phys_addr_t;

typedef phys_addr_t resource_size_t;

typedef struct {
 int counter;
} atomic_t;

struct rcu_head {
 struct rcu_head *next;
 void (*func)(struct rcu_head *head);
};

struct sk_buff;

struct dst_entry {
 struct rcu_head rcu_head;
 struct dst_entry *child;
 struct net_device *dev;
 short error;
 short obsolete;
 int flags;

 unsigned long expires;

 unsigned short header_len;
 unsigned short trailer_len;

 unsigned int rate_tokens;
 unsigned long rate_last;

 struct dst_entry *path;

 struct neighbour *neighbour;
 struct hh_cache *hh;

 struct xfrm_state *xfrm;


 int (*input)(struct sk_buff*);
 int (*output)(struct sk_buff*);

 struct dst_ops *ops;

 u32 metrics[(__RTAX_MAX - 1)];

 __u32 tclassid;
 long __pad_to_align_refcnt[1];

 atomic_t __refcnt;
 int __use;
 unsigned long lastuse;
 union {
  struct dst_entry *next;
  struct rtable *rt_next;
  struct rt6_info *rt6_next;
  struct dn_route *dn_next;
 };
};

// GCC specific
#ifdef __GNUC__
STATIC_ASSERT((__builtin_offsetof(struct dst_entry,__refcnt) & 63)==0);
#endif

int main()
{
}

