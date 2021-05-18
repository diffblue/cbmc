// This file is highly reduced from some open source projects.
// The following four lines are adapted from the openssl library
// Full repository here:
// Exact file adapted from here: https://github.com/openssl/openssl/tree/master
// https://github.com/openssl/openssl/blob/master/crypto/evp/evp_local.h
struct evp_md_ctx_st
{
  const void *digest;
};
// The rest of this file is adapted from, various files in the
// AWS s2n library. Full repository and licence information is
// available here: https://github.com/aws/s2n-tls
// Note that this is a highly cut down synthesis of many files
// with most of their content and structure reduced.
struct s2n_evp_digest
{
  const void *ctx;
};
union s2n_hash_low_level_digest {
};
struct s2n_hash_evp_digest
{
  struct s2n_evp_digest evp_md5_secondary;
};
struct s2n_hash_state
{
  const struct s2n_hash *hash_impl;
  union {
    union s2n_hash_low_level_digest low_level;
    struct s2n_hash_evp_digest high_level;
  } digest;
};
struct s2n_hash
{
  int (*free)(struct s2n_hash_state *state);
};
void EVP_MD_CTX_free(struct evp_md_ctx_st *ctx)
{
  free(ctx->digest);
  free(ctx);
}
static int s2n_evp_hash_free(struct s2n_hash_state *state)
{
  (EVP_MD_CTX_free((state->digest.high_level.evp_md5_secondary.ctx)));
  return 0;
}
static const struct s2n_hash s2n_evp_hash = {
  .free = &s2n_evp_hash_free,
};
static int s2n_hash_set_impl(struct s2n_hash_state *state)
{
  state->hash_impl = &s2n_evp_hash;
  return 0;
}
