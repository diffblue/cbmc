/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// clang-format off

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// iovec
#include <sys/uio.h>
// sysconf
#include <unistd.h>


bool nondet_bool();
int nondet_int();
long nondet_long();

// ============================= SAFETY ==============================

#define S2N_SUCCESS 0
#define S2N_FAILURE -1

#define __S2N_ENSURE( cond, action ) do {if ( !(cond) ) { action; }} while (0)

#define POSIX_GUARD(result)                                   __S2N_ENSURE((result) >= S2N_SUCCESS, return S2N_FAILURE)

#define S2N_IMPLIES(a, b) (!(a) || (b))

typedef struct {
    int __error_signal;
} s2n_result;

inline bool s2n_result_is_ok(s2n_result result)
{
    return result.__error_signal == S2N_SUCCESS;
}

#define s2n_likely(x) __builtin_expect(!!(x), 1)
#define S2N_RESULT_OK ((s2n_result) { S2N_SUCCESS })
#define S2N_RESULT_ERROR ((s2n_result) { S2N_FAILURE })

#define __S2N_ENSURE_PRECONDITION( result ) (s2n_likely(s2n_result_is_ok(result)) ? S2N_RESULT_OK : S2N_RESULT_ERROR)

#define POSIX_GUARD_RESULT(result)                            __S2N_ENSURE(s2n_result_is_ok(result), return S2N_FAILURE)
#define POSIX_PRECONDITION(result)                            POSIX_GUARD_RESULT(__S2N_ENSURE_PRECONDITION((result)))

int s2n_calculate_stacktrace() { return nondet_bool() ? S2N_SUCCESS : S2N_FAILURE; }

__thread int s2n_errno;
__thread const char *s2n_debug_str;

#define TO_STRING(s) #s
#define STRING_(s) TO_STRING(s)
#define STRING__LINE__ STRING_(__LINE__)
#define _S2N_DEBUG_LINE     "Error encountered in " __FILE__ ":" STRING__LINE__


#define _S2N_ERROR( x )     do { s2n_debug_str = _S2N_DEBUG_LINE; s2n_errno = ( x ); s2n_calculate_stacktrace(); } while (0)

#define POSIX_BAIL(error)                                     do { _S2N_ERROR((error)); return S2N_FAILURE; } while (0)
#define POSIX_ENSURE(condition, error)                        __S2N_ENSURE((condition), POSIX_BAIL(error))


// =========================== CBMC MACROS ===========================

#ifdef CBMC
#    define CONTRACT_ASSIGNS(...) __CPROVER_assigns(__VA_ARGS__)
#    define CONTRACT_ASSIGNS_ERR(...) __CPROVER_assigns(s2n_debug_str, s2n_errno; __VA_ARGS__)
#    define CONTRACT_REQUIRES(...) __CPROVER_requires(__VA_ARGS__)
#    define CONTRACT_ENSURES(...) __CPROVER_ensures(__VA_ARGS__)
#    define CONTRACT_INVARIANT(...) __CPROVER_loop_invariant(__VA_ARGS__)
#    define CONTRACT_LOOP_ENTRY(...) __CPROVER_loop_entry(__VA_ARGS__)
#    define CONTRACT_RETURN_VALUE (__CPROVER_return_value)
#    define CONTRACT_IS_FRESH(...) __CPROVER_is_fresh(__VA_ARGS__)
#    define CONTRACT_OLD(...) __CPROVER_old(__VA_ARGS__)
#    define CONTRACT_ENSURES_SUCCESS(...) __CPROVER_ensures(S2N_IMPLIES(CONTRACT_RETURN_VALUE >= S2N_SUCCESS, __VA_ARGS__))
#    define CONTRACT_ENSURES_FAILURE(...) __CPROVER_ensures(S2N_IMPLIES(CONTRACT_RETURN_VALUE <= S2N_FAILURE, __VA_ARGS__))
#    define CONTRACT_ENSURES_VALID_RETURN_VALUE __CPROVER_ensures(__CPROVER_return_value == S2N_SUCCESS || __CPROVER_return_value == S2N_FAILURE)
#    define RW_OK(ptr) __CPROVER_rw_ok(ptr, sizeof(*(ptr)))
#    define RW_OK_SIZE(ptr, size) __CPROVER_rw_ok(ptr, size)
#else
#    define CONTRACT_ASSIGNS(...)
#    define CONTRACT_ASSIGNS_ERR(...)
#    define CONTRACT_REQUIRES(...)
#    define CONTRACT_ENSURES(...)
#    define CONTRACT_INVARIANT(...)
#    define CONTRACT_LOOP_ENTRY(...)
#    define CONTRACT_RETURN_VALUE
#    define CONTRACT_IS_FRESH(...)
#    define CONTRACT_OLD(...)
#    define CONTRACT_ENSURES_SUCCESS(...)
#    define CONTRACT_ENSURES_FAILURE(...)
#    define CONTRACT_ENSURES_VALID_RETURN_VALUE
#    define RW_OK(...)
#    define RW_OK_SIZE(...)
#endif

#define CBMC_ENSURE_REF(cond)    \
    do {                         \
        if (!(cond)) { return; } \
    } while (0)


// ============================ FIPS_MODE ============================

static int __CPROVER_s2n_fips_mode = 0;

void s2n_fips_init(void) {
    __CPROVER_s2n_fips_mode = nondet_int();
}

int s2n_is_in_fips_mode()
{
    return __CPROVER_s2n_fips_mode;
}

// ========================== S2N_MEM_INIT ===========================

static long page_size = 4096;

long sysconf(int name) { return nondet_long(); }


int s2n_mem_init()
{
    POSIX_GUARD(page_size = sysconf(_SC_PAGESIZE));

    return 0;
}

void s2n_mem_init_nondet() {
  if (nondet_bool()) {
    s2n_mem_init();
  }
}


// ============================= BIGNUM ==============================

typedef struct bignum_st BIGNUM;

/* Abstraction of the BIGNUM struct. */
struct bignum_st {
    bool is_initialized;
    unsigned long int *d; /* Pointer to an array of 'BN_BITS2' bit
                           * chunks. */
    int top;              /* Index of last used d +1. */
    /* The next are internal book keeping for bn_expand. */
    int dmax; /* Size of the d array. */
    int neg;  /* one if the number is negative */
    int flags;
};


// ============================== OSSL ===============================

#define MD5_LONG unsigned int
#define MD5_CBLOCK 64
#define MD5_LBLOCK (MD5_CBLOCK / 4)

typedef struct MD5state_st {
    /* Internal buffers used during the computation. */
    MD5_LONG A, B, C, D;
    /* The other subfields keep information on the running hash. */
    MD5_LONG Nl, Nh;
    MD5_LONG data[MD5_LBLOCK];
    unsigned int num;
} MD5_CTX;


#define SHA_LONG unsigned int
#define SHA_LBLOCK 16
#define SHA_CBLOCK                                 \
    (SHA_LBLOCK * 4) /* SHA treats input data as a \
                      * contiguous array of 32 bit \
                      * wide big-endian values. */

typedef struct SHAstate_st {
    SHA_LONG h0, h1, h2, h3, h4;
    SHA_LONG Nl, Nh;
    SHA_LONG data[SHA_LBLOCK];
    unsigned int num;
} SHA_CTX;

typedef struct SHA256state_st {
    SHA_LONG h[8];
    SHA_LONG Nl, Nh;
    SHA_LONG data[SHA_LBLOCK];
    unsigned int num, md_len;
} SHA256_CTX;

#define SHA512_CBLOCK                                  \
    (SHA_LBLOCK * 8) /* SHA-512 treats input data as a \
                      * contiguous array of 64 bit     \
                      * wide big-endian values. */
#define SHA_LONG64 unsigned long long
#define SHA512_DIGEST_LENGTH 64

typedef struct SHA512state_st {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl, Nh;
    union {
        SHA_LONG64 d[SHA_LBLOCK];
        unsigned char p[SHA512_CBLOCK];
    } u;
    unsigned int num, md_len;
} SHA512_CTX;


// =============================== EVP ===============================

enum evp_sha { EVP_MD5, EVP_SHA1, EVP_SHA224, EVP_SHA256, EVP_SHA384, EVP_SHA512 };

typedef struct evp_md_st EVP_MD;
typedef struct evp_md_ctx_st EVP_MD_CTX;
typedef struct evp_pkey_ctx_st EVP_PKEY_CTX;
typedef struct evp_pkey_st EVP_PKEY;
typedef struct ec_key_st EC_KEY;

typedef enum {
    POINT_CONVERSION_COMPRESSED = 2,
    POINT_CONVERSION_UNCOMPRESSED = 4,
    POINT_CONVERSION_HYBRID = 6
} point_conversion_form_t;

/* Abstraction of the EC_GROUP struct */
struct ec_group_st {
    int curve_name;
    point_conversion_form_t asn1_form;
    BIGNUM *order;
};

typedef struct ec_group_st EC_GROUP;

/* Abstraction of the EC_KEY struct */
struct ec_key_st {
    int references;
    EC_GROUP *group;
    point_conversion_form_t conv_form;
    BIGNUM *priv_key;
    bool pub_key_is_set;  // We never have to return a public-key object, so just having this flag is enough
};

struct evp_pkey_st {
    int references;
    EC_KEY *ec_key;
};

struct evp_pkey_ctx_st {
    bool is_initialized_for_signing;
    bool is_initialized_for_derivation;
    bool is_initialized_for_encryption;
    bool is_initialized_for_decryption;
    int rsa_pad;
    EVP_PKEY *pkey;
};

/* Abstraction of the EVP_MD struct. */
struct evp_md_st {
    enum evp_sha from;

    /* nid */
    int type;

    int pkey_type;
    int md_size;
    unsigned long flags;
    int block_size;
    /* How big does the ctx->md_data need to be. */
    int ctx_size;
};


struct evp_md_ctx_st {
    const EVP_MD *digest;

    unsigned long flags;
    void *md_data;
    /* Public key context for sign/verify. */
    EVP_PKEY_CTX *pctx;
} /* EVP_MD_CTX */;


struct s2n_evp_digest {
    const EVP_MD *md;
    EVP_MD_CTX *ctx;
};



// ========================= S2N_HASH_STATE ==========================

typedef enum {
    S2N_HASH_NONE=0,
    S2N_HASH_MD5,
    S2N_HASH_SHA1,
    S2N_HASH_SHA224,
    S2N_HASH_SHA256,
    S2N_HASH_SHA384,
    S2N_HASH_SHA512,
    S2N_HASH_MD5_SHA1,
    /* Don't add any hash algorithms below S2N_HASH_SENTINEL */
    S2N_HASH_SENTINEL
} s2n_hash_algorithm;




/* The low_level_digest stores all OpenSSL structs that are alg-specific to be used with OpenSSL's low-level hash API's. */
union s2n_hash_low_level_digest {
    MD5_CTX md5;
    SHA_CTX sha1;
    SHA256_CTX sha224;
    SHA256_CTX sha256;
    SHA512_CTX sha384;
    SHA512_CTX sha512;
    struct {
        MD5_CTX md5;
        SHA_CTX sha1;
    } md5_sha1;
};

/* The evp_digest stores all OpenSSL structs to be used with OpenSSL's EVP hash API's. */
struct s2n_hash_evp_digest {
    struct s2n_evp_digest evp;
    /* Always store a secondary evp_digest to allow resetting a hash_state to MD5_SHA1 from another alg. */
    struct s2n_evp_digest evp_md5_secondary;
};


struct s2n_hash_state {
    const struct s2n_hash *hash_impl;
    s2n_hash_algorithm alg;
    uint8_t is_ready_for_input;
    uint64_t currently_in_hash;
    union {
        union s2n_hash_low_level_digest low_level;
        struct s2n_hash_evp_digest high_level;
    } digest;
};

struct s2n_hash {
    int (*alloc) (struct s2n_hash_state *state);
    int (*allow_md5_for_fips) (struct s2n_hash_state *state);
    int (*init) (struct s2n_hash_state *state, s2n_hash_algorithm alg);
    int (*update) (struct s2n_hash_state *state, const void *data, uint32_t size);
    int (*digest) (struct s2n_hash_state *state, void *out, uint32_t size);
    int (*copy) (struct s2n_hash_state *to, struct s2n_hash_state *from);
    int (*reset) (struct s2n_hash_state *state);
    int (*free) (struct s2n_hash_state *state);
};


// ========================= S2N_HMAC_STATE ==========================

typedef enum {
    S2N_HMAC_NONE,
    S2N_HMAC_MD5,
    S2N_HMAC_SHA1,
    S2N_HMAC_SHA224,
    S2N_HMAC_SHA256,
    S2N_HMAC_SHA384,
    S2N_HMAC_SHA512,
    S2N_HMAC_SSLv3_MD5,
    S2N_HMAC_SSLv3_SHA1
} s2n_hmac_algorithm;


struct s2n_hmac_state {
    s2n_hmac_algorithm alg;

    uint16_t hash_block_size;
    uint32_t currently_in_hash_block;
    uint16_t xor_pad_size;
    uint8_t digest_size;

    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;
    struct s2n_hash_state outer_just_key;

    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];

    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
};


// ====================== S2N_CRYPTO_PARAMETERS ======================

#define S2N_TLS_SEQUENCE_NUM_LEN        8

struct s2n_crypto_parameters {
    struct s2n_hmac_state client_record_mac;
    struct s2n_hmac_state server_record_mac;
    uint8_t client_sequence_number[S2N_TLS_SEQUENCE_NUM_LEN];
    uint8_t server_sequence_number[S2N_TLS_SEQUENCE_NUM_LEN];
};



// =========================== S2N_STUFFER ===========================

struct s2n_blob {
    /* The data for the s2n_blob */
    uint8_t *data;

    /* The size of the data */
    uint32_t size;

    /* The amount of memory allocated for this blob (i.e. the amount of memory
     * which needs to be freed when the blob is cleaned up). If this blob was
     * created with s2n_blob_init(), this value is 0. If s2n_alloc() was called,
     * this value will be greater than 0.
     */
    uint32_t allocated;

    /* Can this blob be resized */
    unsigned growable :1;
};

struct s2n_stuffer {
    /* The data for the s2n_stuffer */
    struct s2n_blob blob;

    /* Cursors to the current read/write position in the s2n_stuffer */
    uint32_t read_cursor;
    uint32_t write_cursor;
    uint32_t high_water_mark;

    /* Was this stuffer alloc()'d ? */
    unsigned int alloced:1;

    /* Is this stuffer growable? */
    unsigned int growable:1;

    /* Can this stuffer be safely resized?
     * A growable stuffer can be temporarily tainted by a raw read/write,
     * preventing it from resizing. */
    unsigned int tainted:1;
};



// ========================= S2N_CONNECTION ==========================

typedef enum { S2N_SERVER, S2N_CLIENT } s2n_mode;

struct s2n_connection {
    s2n_mode mode;

    struct s2n_crypto_parameters *initial;
    struct s2n_crypto_parameters *secure;

    struct s2n_crypto_parameters *client;
    struct s2n_crypto_parameters *server;

    struct s2n_stuffer out;
};




// ========================= S2N_HMAC_UPDATE =========================

int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
  CONTRACT_REQUIRES(size != 0 && size <= __CPROVER_max_malloc_size)
  CONTRACT_REQUIRES(RW_OK(state))
  CONTRACT_REQUIRES(RW_OK_SIZE(in, size))
  CONTRACT_REQUIRES(S2N_IMPLIES(s2n_is_in_fips_mode(),
                                RW_OK(state->inner.digest.high_level.evp.ctx)
                                && RW_OK(state->inner.digest.high_level.evp.ctx->digest)
                                && RW_OK(state->inner.digest.high_level.evp_md5_secondary.ctx)
                                && RW_OK(state->inner.digest.high_level.evp_md5_secondary.ctx->digest)))
  CONTRACT_ASSIGNS(s2n_debug_str, s2n_errno;
                   state->currently_in_hash_block,
                   state->inner.hash_impl,
                   state->inner.currently_in_hash;
                   s2n_is_in_fips_mode():
                       *(state->inner.digest.high_level.evp.ctx->digest),
                       *(state->inner.digest.high_level.evp_md5_secondary.ctx->digest))
  CONTRACT_ENSURES_VALID_RETURN_VALUE
{
    return 0;
}


// ======================== S2N_RECORD_WRITEV ========================

#define S2N_TLS_SEQUENCE_NUM_LEN        8
#define S2N_TLS_CONTENT_TYPE_LENGTH             1
#define S2N_TLS_PROTOCOL_VERSION_LEN    2
#define S2N_TLS_RECORD_HEADER_LENGTH            (S2N_TLS_CONTENT_TYPE_LENGTH + S2N_TLS_PROTOCOL_VERSION_LEN + 2)


int s2n_record_writev(struct s2n_connection *conn, uint8_t content_type, const struct iovec *in, size_t in_count, size_t offs, size_t to_write)
    CONTRACT_REQUIRES(conn != NULL)
    CONTRACT_REQUIRES(conn->initial != NULL)
    CONTRACT_REQUIRES(conn->client != NULL)
    CONTRACT_REQUIRES(conn->server != NULL)
    CONTRACT_REQUIRES(S2N_IMPLIES(s2n_is_in_fips_mode(),
                      RW_OK(conn->client->client_record_mac.inner.digest.high_level.evp.ctx)
                      && RW_OK(conn->client->client_record_mac.inner.digest.high_level.evp.ctx->digest)
                      && RW_OK(conn->client->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx)
                      && RW_OK(conn->client->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest)
                      && RW_OK(conn->server->server_record_mac.inner.digest.high_level.evp.ctx)
                      && RW_OK(conn->server->server_record_mac.inner.digest.high_level.evp.ctx->digest)
                      && RW_OK(conn->server->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx)
                      && RW_OK(conn->server->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest)
                      && RW_OK(conn->initial->client_record_mac.inner.digest.high_level.evp.ctx)
                      && RW_OK(conn->initial->client_record_mac.inner.digest.high_level.evp.ctx->digest)
                      && RW_OK(conn->initial->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx)
                      && RW_OK(conn->initial->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest)
                      && RW_OK(conn->initial->server_record_mac.inner.digest.high_level.evp.ctx)
                      && RW_OK(conn->initial->server_record_mac.inner.digest.high_level.evp.ctx->digest)
                      && RW_OK(conn->initial->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx)
                      && RW_OK(conn->initial->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest)))
CONTRACT_ASSIGNS(s2n_debug_str, s2n_errno;
                     conn->initial,
                     conn->server,
                     conn->client,
                     conn->out,
                     __CPROVER_object_upto(conn->out.blob.data, conn->out.blob.size),

                     conn->initial->client_sequence_number,
                     conn->initial->client_record_mac.inner.hash_impl,
                     conn->initial->client_record_mac.inner.currently_in_hash,
                     conn->initial->client_record_mac.currently_in_hash_block,
                     conn->initial->server_sequence_number,
                     conn->initial->server_record_mac.inner.hash_impl,
                     conn->initial->server_record_mac.inner.currently_in_hash,
                     conn->initial->server_record_mac.currently_in_hash_block,
                     conn->client->client_sequence_number,
                     conn->client->client_record_mac.inner.hash_impl,
                     conn->client->client_record_mac.inner.currently_in_hash,
                     conn->client->client_record_mac.currently_in_hash_block,
                     conn->server->server_sequence_number,
                     conn->server->server_record_mac.inner.hash_impl,
                     conn->server->server_record_mac.inner.currently_in_hash,
                     conn->server->server_record_mac.currently_in_hash_block;
                     s2n_is_in_fips_mode():
                        *(conn->initial->client_record_mac.inner.digest.high_level.evp.ctx->digest),
                        *(conn->initial->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest),
                        *(conn->initial->server_record_mac.inner.digest.high_level.evp.ctx->digest),
                        *(conn->initial->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest),
                        *(conn->client->client_record_mac.inner.digest.high_level.evp.ctx->digest),
                        *(conn->client->client_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest),
                        *(conn->server->server_record_mac.inner.digest.high_level.evp.ctx->digest),
                        *(conn->server->server_record_mac.inner.digest.high_level.evp_md5_secondary.ctx->digest)
    )
{
    /* if (conn->actual_protocol_version == S2N_TLS13 && content_type == TLS_CHANGE_CIPHER_SPEC) { */
    // THIS IS NECESSARY FOR HANG
    conn->client = conn->initial;
    conn->server = conn->initial;
    /* } */

    /* uint8_t *sequence_number = conn->server->server_sequence_number; */
    /* struct s2n_hmac_state *mac = &conn->server->server_record_mac; */
    uint8_t *sequence_number;
    struct s2n_hmac_state *mac;

    if (conn->mode == S2N_CLIENT) {
        sequence_number = conn->client->client_sequence_number;
        mac = &conn->client->client_record_mac;
    } else {
        sequence_number = conn->server->server_sequence_number;
        mac = &conn->server->server_record_mac;
    }

    /* Start the MAC with the sequence number */
    POSIX_GUARD(s2n_hmac_update(mac, sequence_number, S2N_TLS_SEQUENCE_NUM_LEN));

    // BOGUS ASSIGNMENT
    /* mac->inner.hash_impl = &s2n_evp_hash; */

    /* if (conn->actual_protocol_version > S2N_SSLv3) { */
        POSIX_GUARD(s2n_hmac_update(mac, conn->out.blob.data, S2N_TLS_RECORD_HEADER_LENGTH));
    /* } */

    return 0;
}


// ============================ POPULATE =============================

void cbmc_populate_BIGNUM(BIGNUM *bignum)
{
    CBMC_ENSURE_REF(bignum);
    bignum->d = malloc(sizeof(*(bignum->d)));
}

BIGNUM *cbmc_allocate_BIGNUM()
{
    BIGNUM *bignum = malloc(sizeof(*bignum));
    cbmc_populate_BIGNUM(bignum);
    return bignum;
}


void cbmc_populate_EC_GROUP(EC_GROUP *ec_group)
{
    CBMC_ENSURE_REF(ec_group);
    ec_group->order = cbmc_allocate_BIGNUM();
}


EC_GROUP *cbmc_allocate_EC_GROUP()
{
    EC_GROUP *ec_group = malloc(sizeof(*ec_group));
    cbmc_populate_EC_GROUP(ec_group);
    return ec_group;
}


void cbmc_populate_EC_KEY(EC_KEY *ec_key)
{
    CBMC_ENSURE_REF(ec_key);
    ec_key->group    = cbmc_allocate_EC_GROUP();
    ec_key->priv_key = cbmc_allocate_BIGNUM();
}


EC_KEY *cbmc_allocate_EC_KEY()
{
    EC_KEY *ec_key = malloc(sizeof(*ec_key));
    cbmc_populate_EC_KEY(ec_key);
    return ec_key;
}


void cbmc_populate_EVP_PKEY(EVP_PKEY *evp_pkey)
{
    CBMC_ENSURE_REF(evp_pkey);
    evp_pkey->ec_key = cbmc_allocate_EC_KEY();
}


EVP_PKEY *cbmc_allocate_EVP_PKEY()
{
    EVP_PKEY *evp_pkey = malloc(sizeof(*evp_pkey));
    cbmc_populate_EVP_PKEY(evp_pkey);
    return evp_pkey;
}

void cbmc_populate_EVP_PKEY_CTX(EVP_PKEY_CTX *evp_pkey_ctx)
{
    CBMC_ENSURE_REF(evp_pkey_ctx);
    evp_pkey_ctx->pkey = cbmc_allocate_EVP_PKEY();
}


EVP_PKEY_CTX *cbmc_allocate_EVP_PKEY_CTX()
{
    EVP_PKEY_CTX *evp_pkey_ctx = malloc(sizeof(*evp_pkey_ctx));
    cbmc_populate_EVP_PKEY_CTX(evp_pkey_ctx);
    return evp_pkey_ctx;
}


#define EVP_MAX_MD_SIZE 64                    /* Longest known is SHA512. */

void cbmc_populate_EVP_MD_CTX(EVP_MD_CTX *ctx)
{
    CBMC_ENSURE_REF(ctx);
    ctx->digest  = malloc(sizeof(*(ctx->digest)));
    ctx->md_data = malloc(EVP_MAX_MD_SIZE);
    ctx->pctx    = cbmc_allocate_EVP_PKEY_CTX();
}

EVP_MD_CTX *cbmc_allocate_EVP_MD_CTX()
{
    EVP_MD_CTX *ctx = malloc(sizeof(*ctx));
    cbmc_populate_EVP_MD_CTX(ctx);
    return ctx;
}

void cbmc_populate_s2n_evp_digest(struct s2n_evp_digest *evp_digest) {
    CBMC_ENSURE_REF(evp_digest);
    /* `evp_digest->md` is never allocated.
     * It is always initialized based on the hashing algorithm.
     * If required, this initialization should be done in the validation function.
     */
    evp_digest->ctx = cbmc_allocate_EVP_MD_CTX();
}


void cbmc_populate_s2n_hash_state(struct s2n_hash_state* state)
{
    CBMC_ENSURE_REF(state);
    /* `state->hash_impl` is never allocated.
     * It is always initialized based on the hashing algorithm.
     * If required, this initialization should be done in the validation function.
     */
    cbmc_populate_s2n_evp_digest(&state->digest.high_level.evp);
    cbmc_populate_s2n_evp_digest(&state->digest.high_level.evp_md5_secondary);
}

void cbmc_populate_s2n_hmac_state(struct s2n_hmac_state *state)
{
    CBMC_ENSURE_REF(state);
    cbmc_populate_s2n_hash_state(&state->inner);
    cbmc_populate_s2n_hash_state(&state->inner_just_key);
    cbmc_populate_s2n_hash_state(&state->outer);
    cbmc_populate_s2n_hash_state(&state->outer_just_key);
}



void cbmc_populate_s2n_blob(struct s2n_blob *blob)
{
    CBMC_ENSURE_REF(blob);
    if (blob->growable) {
        blob->data = (blob->allocated == 0) ? NULL : malloc(blob->allocated);
    } else {
        blob->data = (blob->size == 0) ? NULL : malloc(blob->size);
    }
}

void cbmc_populate_s2n_stuffer(struct s2n_stuffer *stuffer)
{
    CBMC_ENSURE_REF(stuffer);
    cbmc_populate_s2n_blob(&stuffer->blob);
}

struct s2n_stuffer *cbmc_allocate_s2n_stuffer()
{
    struct s2n_stuffer *stuffer = malloc(sizeof(*stuffer));
    cbmc_populate_s2n_stuffer(stuffer);
    return stuffer;
}



// ============================= HARNESS =============================

void s2n_record_writev_harness()
{
  /* Non-deterministic input allocation. */
  struct s2n_connection *conn = malloc(sizeof(*conn));


  struct s2n_hmac_state client_record_mac;
  cbmc_populate_s2n_hmac_state(&(client_record_mac));
  /* __CPROVER_assume(s2n_result_is_ok(s2n_hmac_state_validate(&(client_record_mac)))); */
  /* __CPROVER_file_local_s2n_hash_c_s2n_hash_set_impl(&(client_record_mac)); */
  struct s2n_hmac_state server_record_mac;
  cbmc_populate_s2n_hmac_state(&(server_record_mac));
  /* __CPROVER_assume(s2n_result_is_ok(s2n_hmac_state_validate(&(server_record_mac)))); */
  /* __CPROVER_file_local_s2n_hash_c_s2n_hash_set_impl(&(server_record_mac)); */
  
  struct s2n_stuffer *conn_out = cbmc_allocate_s2n_stuffer();
  /* __CPROVER_assume(s2n_result_is_ok(s2n_stuffer_validate(conn_out))); */
  
  if(conn) {
    conn->out = *conn_out;
    /* initial */
    conn->initial = malloc(sizeof(*(conn->initial)));
    if(conn->initial) {
        conn->initial->client_record_mac = client_record_mac;
        conn->initial->server_record_mac = server_record_mac;
    }

    /* client */
    conn->client = malloc(sizeof(*(conn->client)));
    if(conn->client) {
      conn->client->client_record_mac = client_record_mac;
    }  

    /* server */
    conn->server = malloc(sizeof(*(conn->server)));
    if(conn->server) {
      conn->server->server_record_mac = server_record_mac;
    }
    
  }
  uint8_t content_type;
  const struct iovec *in = malloc(sizeof(*in));
  size_t in_count;
  uint32_t offs;
  size_t to_write;

  /* Extra assumptions. */
  s2n_mem_init_nondet();

  /* Initialize s2n_fips_mode nondetermistically. Check stub for
   * details */
  s2n_fips_init();
  
  /* Operation under verification. */
  s2n_record_writev(conn, content_type, in, in_count, offs, to_write);
}

// clang-format on
