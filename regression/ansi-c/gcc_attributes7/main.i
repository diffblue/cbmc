struct X {
  int a;
};

struct S {
 struct X x __attribute__((aligned(
# 81 "ring.h" 3 4
                         16
# 81 "ring.h"
                         )));
 struct X x2 __attribute__((aligned(
# 82 "ring.h" 3 4
                        (((
# 82 "ring.h"
                        sizeof(struct X)
# 82 "ring.h" 3 4
                        )+16 -1)&~(16 -1))
# 82 "ring.h"
                        )));
};

typedef int int8_t
# 194 "/usr/include/x86_64-linux-gnu/sys/types.h"
__attribute__(
# 194 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
(__mode__ (__QI__))
# 194 "/usr/include/x86_64-linux-gnu/sys/types.h"
)
# 194 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
                   ;

int extundelete_process_dir_block(int fs,
        int b
# 29 "block.h" 3 4
                         __attribute__(
# 29 "block.h"
                         (unused)
# 29 "block.h" 3 4
                         )
# 29 "block.h"
                                              ,
        int ref_offset
# 30 "block.h" 3 4
                      __attribute__(
# 30 "block.h"
                      (unused)
# 30 "block.h" 3 4
                      )
# 30 "block.h"
                                           ,
        void *priv_data);

int main()
{
}
