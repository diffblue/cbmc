typedef long int off_t;
typedef signed char smallint;

typedef struct chain_s {
  struct node_s *first;
  struct node_s *last;
  const char *programname;
} chain;

typedef struct func_s {
    struct chain_s body;
} func;

typedef struct node_s {
  struct node_s *n;
} node;

typedef struct dumper_t_x {
  node n;
  off_t dump_skip;
  signed int dump_length;
  smallint dump_vflag;
} dumper_t;

typedef struct FS_x {
  struct FS *nextfs;
  signed int bcnt;
} FS;

dumper_t * alloc_dumper(void) {
  return (void*) 0;
}

typedef unsigned int uint32_t;

const uint32_t xx[2];

typedef struct node_s2 {
  uint32_t info;
} node2;

typedef struct {
  int x;
} anon_name;

typedef struct node_s3 {
  union {
    struct node_s *n;
    func *f;
  } r;
} node3;

typedef int x_int;
typedef int y_int;
typedef x_int *p_int;

int main() {
  node n;
  chain c;
  dumper_t a;
  dumper_t b[3];
  node2* sn;
  anon_name d;
  node3* s3;
  y_int y;
  p_int p;
  alloc_dumper();
  return 0;
}
