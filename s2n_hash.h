#include <vcc.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

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
        //_(invariant \mine((SHA_LONG[SHA_LBLOCK])data))
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
int SHA1_Init(SHA_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
;

int SHA224_Init(SHA256_CTX *c);
int SHA256_Init(SHA256_CTX *c);
int SHA384_Init(SHA512_CTX *c);
int SHA512_Init(SHA512_CTX *c);

int SHA1_Update(SHA_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(requires \thread_local_array(data,len))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
;

int SHA1_Final(void *md, SHA_CTX *c)
    _(requires \wrapped(c) && \mutable(md))
    _(writes md, c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
;

#define eq_check(a, b)  do { if ( (a) != (b) ) {/* S2N_ERROR(S2N_ERR_SAFETY)*/ return -1; } } while(0)

typedef enum { S2N_HASH_NONE, S2N_HASH_MD5, S2N_HASH_SHA1, S2N_HASH_SHA224, S2N_HASH_SHA256, S2N_HASH_SHA384,
    S2N_HASH_SHA512, S2N_HASH_MD5_SHA1
} s2n_hash_algorithm; 

typedef _(dynamic_owns) struct s2n_hash_state {
    s2n_hash_algorithm alg;
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
    _(invariant \mine(&hash_ctx.sha1))
    _(invariant alg == S2N_HASH_SHA1)
    _(invariant alg == S2N_HASH_MD5 ==> \union_active(&hash_ctx.md5) && \mine(&hash_ctx.md5))
    _(invariant alg == S2N_HASH_SHA1 ==> \union_active(&hash_ctx.sha1) && \mine(&hash_ctx.sha1))
    _(invariant alg == S2N_HASH_SHA224 ==> \union_active(&hash_ctx.sha224) && \mine(&hash_ctx.sha224))
    _(invariant alg == S2N_HASH_SHA256 ==> \union_active(&hash_ctx.sha256) && \mine(&hash_ctx.sha256))
    _(invariant alg == S2N_HASH_SHA384 ==> \union_active(&hash_ctx.sha384) && \mine(&hash_ctx.sha384))
    _(invariant alg == S2N_HASH_SHA512 ==> \union_active(&hash_ctx.sha512) && \mine(&hash_ctx.sha512))
    _(invariant alg == S2N_HASH_MD5_SHA1 ==> \union_active(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1))
    _(invariant \mine(&hash_ctx))
};

extern int s2n_hash_digest_size(s2n_hash_algorithm alg)
    _(requires 0 <= alg && alg <= 7)
    _(ensures alg == S2N_HASH_NONE ==> \result == 0)
    _(ensures alg == S2N_HASH_MD5 ==> \result == MD5_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_SHA1 ==> \result == SHA_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_SHA224 ==> \result == SHA224_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_SHA256 ==> \result == SHA256_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_SHA384 ==> \result == SHA384_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_SHA512 ==> \result == SHA512_DIGEST_LENGTH)
    _(ensures alg == S2N_HASH_MD5_SHA1 ==> \result == MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH)
;

int s2n_hash_digest_size(s2n_hash_algorithm alg)
{
    int sizes[] = { 0, MD5_DIGEST_LENGTH, SHA_DIGEST_LENGTH, SHA224_DIGEST_LENGTH, SHA256_DIGEST_LENGTH, SHA384_DIGEST_LENGTH, SHA512_DIGEST_LENGTH, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH };

    return sizes[alg];
}

extern int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
    _(requires alg == S2N_HASH_SHA1)
    _(requires \extent_mutable(state))
    _(writes \extent(state))
    _(ensures \result <= 0)
    _(ensures state->alg == alg)
    _(ensures \wrapped(state))
    _(ensures \fresh(&state->hash_ctx.sha1) && \fresh(&state->hash_ctx))
;

int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
{
    int r;
    switch (alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        r = MD5_Init(&state->hash_ctx.md5);
        break;
    case S2N_HASH_SHA1:
        _(union_reinterpret &state->hash_ctx.sha1)
        r = SHA1_Init(&state->hash_ctx.sha1);
        break;
    case S2N_HASH_SHA224:
        r = SHA224_Init(&state->hash_ctx.sha224);
        break;
    case S2N_HASH_SHA256:
        r = SHA256_Init(&state->hash_ctx.sha256);
        break;
    case S2N_HASH_SHA384:
        r = SHA384_Init(&state->hash_ctx.sha384);
        break;
    case S2N_HASH_SHA512:
        r = SHA512_Init(&state->hash_ctx.sha512);
        break;
    case S2N_HASH_MD5_SHA1:
        r = SHA1_Init(&state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Init(&state->hash_ctx.md5_sha1.md5);
        break;

    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        return -1;
    }

    /*if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_INIT_FAILED);
        //return -1;
    }*/

    state->alg = alg;
    if(alg==S2N_HASH_SHA1) {
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha1, &state->hash_ctx})
        _(wrap state);
    }
    
    return 0;
}

extern int s2n_hash_update(struct s2n_hash_state *state, const void *in, uint32_t size)
    _(requires \wrapped(state))
    _(requires \thread_local_array(in,size))
    _(writes state)
    _(ensures \result == 0)
    _(ensures \wrapped(state))
;

int s2n_hash_update(struct s2n_hash_state *state, const void *data, uint32_t size)
{
    int r;
    _(unwrap state)
    //_(unwrap &state->hash_ctx)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        //r = MD5_Update(&state->hash_ctx.md5, data, size);
        break;
    case S2N_HASH_SHA1:
        r = SHA1_Update(&state->hash_ctx.sha1, data, size);
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

    /*if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        return -1;
    }*/
    //_(wrap &state->hash_ctx)
    _(wrap state)
    return 0;
}

extern int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state) && \mutable(outt))
    _(requires state->alg == S2N_HASH_SHA1 ==> size == SHA_DIGEST_LENGTH)
    _(writes state, outt)
    _(ensures \result <= 0)
    _(ensures \wrapped(state))
;

int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
{
    int r;
    _(assert state->alg == S2N_HASH_SHA1)
    _(unwrap state)
    _(unwrap &state->hash_ctx)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        //eq_check(size, MD5_DIGEST_LENGTH);
        //r = MD5_Final(out, &state->hash_ctx.md5);
        break;
    case S2N_HASH_SHA1:
        eq_check(size, SHA_DIGEST_LENGTH);
        r = SHA1_Final(outt, &state->hash_ctx.sha1);
        break;
    case S2N_HASH_SHA224:
        //eq_check(size, SHA224_DIGEST_LENGTH);
        //r = SHA224_Final(out, &state->hash_ctx.sha224);
        break;
    case S2N_HASH_SHA256:
        //eq_check(size, SHA256_DIGEST_LENGTH);
        //r = SHA256_Final(out, &state->hash_ctx.sha256);
        break;
    case S2N_HASH_SHA384:
        //eq_check(size, SHA384_DIGEST_LENGTH);
        //r = SHA384_Final(out, &state->hash_ctx.sha384);
        break;
    case S2N_HASH_SHA512:
        //eq_check(size, SHA512_DIGEST_LENGTH);
        //r = SHA512_Final(out, &state->hash_ctx.sha512);
        break;
    case S2N_HASH_MD5_SHA1:
        //eq_check(size, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH);
        //r = SHA1_Final(((uint8_t *) out) + MD5_DIGEST_LENGTH, &state->hash_ctx.md5_sha1.sha1);
        //r &= MD5_Final(out, &state->hash_ctx.md5_sha1.md5);
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        return -1;
    }

    /*if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_DIGEST_FAILED);
        return -1;
    }*/
    _(wrap &state->hash_ctx)
    _(wrap state)
    return 0;
}

extern int s2n_hash_reset(struct s2n_hash_state *state)
    _(requires \wrapped(state))
    _(writes state)
    _(ensures \wrapped(state))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->alg))
;

int s2n_hash_reset(struct s2n_hash_state *state)
{
    _(unwrap state)
    _(unwrap &state->hash_ctx)
    _(unwrap &state->hash_ctx.sha1)
    _(union_reinterpret &state->hash_ctx.sha1)
    return s2n_hash_init(state, state->alg);
}

extern int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
    _(requires \extent_mutable(to))
    _(requires to->alg == S2N_HASH_SHA1)
    _(requires \wrapped(from))
    _(requires from != to)
    _(writes \extent(to))
    _(ensures \wrapped(from) && \wrapped(to))
    _(ensures \result <= 0)
; 

int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
{
    memcpy/*_check*/(to, from, sizeof(struct s2n_hash_state));
    _(union_reinterpret &to->hash_ctx.sha1)
    _(wrap &to->hash_ctx)
    _(wrap &to->hash_ctx.sha1)
    _(ghost to->\owns = {&to->hash_ctx.sha1, &to->hash_ctx})
    _(wrap to)
    return 0;
}
