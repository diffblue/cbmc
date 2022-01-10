#include <stdbool.h>

typedef struct CTX
{
  int data[16];
} CTX;

union low_level_t {
  CTX md5;
};

typedef struct HIGH_LEVEL_MD
{
  unsigned long flags;
} HIGH_LEVEL_MD;

typedef struct HIGH_LEVEL_MD_CTX
{
  HIGH_LEVEL_MD *digest;
  unsigned long flags;
} HIGH_LEVEL_MD_CTX;

struct high_level_digest_t
{
  HIGH_LEVEL_MD_CTX *ctx;
};

struct high_level_t
{
  struct high_level_digest_t first;
  struct high_level_digest_t second;
};

typedef struct state_t
{
  union {
    union low_level_t low_level;
    struct high_level_t high_level;
  } digest;
} state_t;

bool nondet_bool();

bool is_high_level()
{
  static bool latch = false;
  static bool once = false;
  if(!once)
  {
    latch = nondet_bool();
    once = true;
  }
  return latch;
}

int update(state_t *state, bool also_second)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(state, sizeof(*state)))
__CPROVER_requires(
  is_high_level() ==> 
    __CPROVER_is_fresh(state->digest.high_level.first.ctx, 
              sizeof(*(state->digest.high_level.first.ctx))) &&
    __CPROVER_is_fresh(state->digest.high_level.first.ctx->digest, 
              sizeof(*(state->digest.high_level.first.ctx->digest))))
__CPROVER_requires(
  is_high_level() && also_second ==>
    __CPROVER_is_fresh(state->digest.high_level.second.ctx, 
              sizeof(*(state->digest.high_level.second.ctx))) &&
    __CPROVER_is_fresh(state->digest.high_level.second.ctx->digest, 
              sizeof(*(state->digest.high_level.second.ctx->digest))))
__CPROVER_assigns(
  is_high_level():
    __CPROVER_POINTER_OBJECT(state->digest.high_level.first.ctx->digest),
    state->digest.high_level.first.ctx->flags;
  is_high_level() && also_second:
    __CPROVER_POINTER_OBJECT(state->digest.high_level.second.ctx->digest),  
    state->digest.high_level.second.ctx->flags;
)
// clang-format on
{
  if(is_high_level())
  {
    // must pass
    __CPROVER_havoc_object(state->digest.high_level.first.ctx->digest);
    state->digest.high_level.first.ctx->flags = 0;

    if(also_second)
    {
      // must pass
      __CPROVER_havoc_object(state->digest.high_level.second.ctx->digest);
      state->digest.high_level.second.ctx->flags = 0;
    }

    // must fail
    __CPROVER_havoc_object(state->digest.high_level.second.ctx->digest);
    state->digest.high_level.second.ctx->flags = 0;
  }

  // must fail
  __CPROVER_havoc_object(state->digest.high_level.first.ctx->digest);
  state->digest.high_level.first.ctx->flags = 0;

  // must fail
  __CPROVER_havoc_object(state->digest.high_level.second.ctx->digest);
  state->digest.high_level.second.ctx->flags = 0;

  return 0;
}

int main()
{
  state_t *state;
  bool also_second;
  update(state, also_second);
  return 0;
}
