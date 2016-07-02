#include <vcc.h>
#include <stdint.h>

#if defined(__LP32__)
#define MD5_LONG unsigned long
#elif defined(OPENSSL_SYS_CRAY) || defined(__ILP64__)
#define MD5_LONG unsigned long
#define MD5_LONG_LOG2 3
#else
#define MD5_LONG unsigned int
#endif

#define MD5_CBLOCK	64
#define MD5_LBLOCK	(MD5_CBLOCK/4)
#define MD5_DIGEST_LENGTH 16
typedef struct MD5state_st
	{
	MD5_LONG A,B,C,D;
	MD5_LONG Nl,Nh;
	MD5_LONG data[MD5_LBLOCK];
	unsigned int num;
	} MD5_CTX;

#if (defined(_WIN32) || defined(_WIN64)) && !defined(__MINGW32__)
#if defined(__LP32__)
#define SHA_LONG unsigned long
#elif defined(OPENSSL_SYS_CRAY) || defined(__ILP64__)
#define SHA_LONG unsigned long
#define SHA_LONG_LOG2 3
#else
#define SHA_LONG unsigned int
#endif
#define SHA_LBLOCK	16
#define SHA_DIGEST_LENGTH 20
#define SHA224_DIGEST_LENGTH	28
#define SHA256_DIGEST_LENGTH	32
#define SHA384_DIGEST_LENGTH	48
#define SHA512_DIGEST_LENGTH	64
typedef struct SHAstate_st
	{
	SHA_LONG h0,h1,h2,h3,h4;
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num;
	} SHA_CTX;
typedef struct SHA256state_st
	{
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num,md_len;
	} SHA256_CTX;
#endif

#ifndef OPENSSL_NO_SHA512
/*
 * Unlike 32-bit digest algorithms, SHA-512 *relies* on SHA_LONG64
 * being exactly 64-bit wide. See Implementation Notes in sha512.c
 * for further details.
 */
#define SHA512_CBLOCK	(SHA_LBLOCK*8)	/* SHA-512 treats input data as a
					 * contiguous array of 64 bit
					 * wide big-endian values. */
#if (defined(_WIN32) || defined(_WIN64)) && !defined(__MINGW32__)
#define SHA_LONG64 unsigned __int64
#define U64(C)     C##UI64
#elif defined(__arch64__)
#define SHA_LONG64 unsigned long
#define U64(C)     C##UL
#else
#define SHA_LONG64 unsigned long long
#define U64(C)     C##ULL
#endif
typedef struct SHA512state_st
	{
	SHA_LONG64 h[8];
	SHA_LONG64 Nl,Nh;
	union {
        struct{SHA_LONG64	d[SHA_LBLOCK];}d;
        struct{unsigned char	p[SHA512_CBLOCK];}p;
	} u;
	unsigned int num,md_len;
	} SHA512_CTX;
#endif

int MD5_Init(MD5_CTX *c);
int SHA1_Init(SHA_CTX *c);
int SHA224_Init(SHA256_CTX *c);
int SHA256_Init(SHA256_CTX *c);
int SHA384_Init(SHA512_CTX *c);
int SHA512_Init(SHA512_CTX *c);

typedef enum { S2N_HASH_NONE, S2N_HASH_MD5, S2N_HASH_SHA1, S2N_HASH_SHA224, S2N_HASH_SHA256, S2N_HASH_SHA384,
    S2N_HASH_SHA512, S2N_HASH_MD5_SHA1
} s2n_hash_algorithm; // as in, a s2n_hash_algorithm can only be of one of these types

typedef _(dynamic_owns) struct s2n_hash_state {
    s2n_hash_algorithm alg;
    _(ghost int tag)
    union {
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
    } hash_ctx;
    _(invariant tag==1)
    _(invariant tag == 0 ==> \union_active(&hash_ctx.md5) && \mine(&hash_ctx.md5))
    _(invariant tag == 1 ==> \union_active(&hash_ctx.sha1) && \mine(&hash_ctx.sha1))
    _(invariant tag == 2 ==> \union_active(&hash_ctx.sha224) && \mine(&hash_ctx.sha224))
    _(invariant tag == 3 ==> \union_active(&hash_ctx.sha256) && \mine(&hash_ctx.sha256))
    _(invariant tag == 4 ==> \union_active(&hash_ctx.sha384) && \mine(&hash_ctx.sha384))
    _(invariant tag == 5 ==> \union_active(&hash_ctx.sha512) && \mine(&hash_ctx.sha512))
    _(invariant tag == 6 ==> \union_active(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1))
};

extern int s2n_hash_digest_size(s2n_hash_algorithm alg)
_(requires alg >= 0 && alg <= 7)
_(ensures alg == 0 ==> \result == 0)
_(ensures alg == 1 ==> \result == MD5_DIGEST_LENGTH)
_(ensures alg == 2 ==> \result == SHA_DIGEST_LENGTH)
_(ensures alg == 3 ==> \result == SHA224_DIGEST_LENGTH)
_(ensures alg == 4 ==> \result == SHA256_DIGEST_LENGTH)
_(ensures alg == 5 ==> \result == SHA384_DIGEST_LENGTH)
_(ensures alg == 6 ==> \result == SHA512_DIGEST_LENGTH)
_(ensures alg == 7 ==> \result == MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH)
;

int s2n_hash_digest_size(s2n_hash_algorithm alg)
{
    int sizes[] = { 0, MD5_DIGEST_LENGTH, SHA_DIGEST_LENGTH, SHA224_DIGEST_LENGTH, SHA256_DIGEST_LENGTH, SHA384_DIGEST_LENGTH, SHA512_DIGEST_LENGTH, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH };

    return sizes[alg];
}

extern int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
_(requires alg >= 0 && alg <= 7)
_(requires \extent_mutable(state))
_(writes \extent(state))
_(ensures \result <= 0)
_(ensures !\result ==> state->alg == alg)
;

int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
{
    int r;
    switch (alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        //r = MD5_Init(&state->hash_ctx.md5);
        break;
    case S2N_HASH_SHA1:
        //r = SHA1_Init(&state->hash_ctx.sha1);
        break;
    case S2N_HASH_SHA224:
        //r = SHA224_Init(&state->hash_ctx.sha224);
        break;
    case S2N_HASH_SHA256:
        //r = SHA256_Init(&state->hash_ctx.sha256);
        break;
    case S2N_HASH_SHA384:
        //r = SHA384_Init(&state->hash_ctx.sha384);
        break;
    case S2N_HASH_SHA512:
        //r = SHA512_Init(&state->hash_ctx.sha512);
        break;
    case S2N_HASH_MD5_SHA1:
        //r = SHA1_Init(&state->hash_ctx.md5_sha1.sha1);
        //r &= MD5_Init(&state->hash_ctx.md5_sha1.md5);
        break;

    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        return -1;
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_INIT_FAILED);
        return -1;
    }

    state->alg = alg;
    _(ghost state->tag = 1)
    _(union_reinterpret &(state->hash_ctx.sha1))
    _(wrap &(state->hash_ctx.sha1))
    _(ghost state->\owns = {&(state->hash_ctx.sha1)})
    _(wrap state)
    return 0;
}

extern int s2n_hash_update(struct s2n_hash_state *state, const void *in, uint32_t size)
_(requires \wrapped(state))
_(ensures \result <= 0)
_(ensures !\result ==> \wrapped(state))
;


int s2n_hash_update(struct s2n_hash_state *state, const void *data, uint32_t size)
{
    int r;
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        //r = MD5_Update(&state->hash_ctx.md5, data, size);
        break;
    case S2N_HASH_SHA1:
        //r = SHA1_Update(&state->hash_ctx.sha1, data, size);
        break;
    case S2N_HASH_SHA224:
        //r = SHA224_Update(&state->hash_ctx.sha224, data, size);
        break;
    case S2N_HASH_SHA256:
        //r = SHA256_Update(&state->hash_ctx.sha256, data, size);
        break;
    case S2N_HASH_SHA384:
        //r = SHA384_Update(&state->hash_ctx.sha384, data, size);
        break;
    case S2N_HASH_SHA512:
        //r = SHA512_Update(&state->hash_ctx.sha512, data, size);
        break;
    case S2N_HASH_MD5_SHA1:
        //r = SHA1_Update(&state->hash_ctx.md5_sha1.sha1, data, size);
        //r &= MD5_Update(&state->hash_ctx.md5_sha1.md5, data, size);
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        return -1;
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        return -1;
    }

    return 0;
}