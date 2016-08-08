#include <vcc.h>
#include <stdint.h>
#include <stdio.h>
#include "num.h"
#include <stdlib.h>

typedef enum { S2N_HASH_NONE, S2N_HASH_MD5, S2N_HASH_SHA1, S2N_HASH_SHA224, S2N_HASH_SHA256, S2N_HASH_SHA384,
    S2N_HASH_SHA512, S2N_HASH_MD5_SHA1
} s2n_hash_algorithm; 

_(ghost _(pure) Num hashVal(Num state, s2n_hash_algorithm alg)
  _(decreases 0))

#define MD5_LONG unsigned int
#define MD5_CBLOCK	64
#define MD5_LBLOCK	(MD5_CBLOCK/4)
#define MD5_DIGEST_LENGTH 16
typedef struct MD5state_st
	{
	MD5_LONG A,B,C,D;
	MD5_LONG Nl,Nh;
	MD5_LONG data[MD5_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
	} MD5_CTX;

typedef struct MD5state_st2
	{
	MD5_LONG A,B,C,D;
	MD5_LONG Nl,Nh;
	MD5_LONG data[MD5_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(invariant valid(val))
    //(invariant val == hashState(\this))
	} MD5_CTX2;

int MD5_Init(MD5_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int MD5_Init2(MD5_CTX2 *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int MD5_Update(MD5_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int MD5_Update2(MD5_CTX2 *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int MD5_Final(void *md, MD5_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md, MD5_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, MD5_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_MD5))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

int MD5_Final2(void *md, MD5_CTX2 *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md,  MD5_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, MD5_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_MD5))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

#define SHA_LONG unsigned int
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
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
	} SHA_CTX;

typedef struct SHAstate_st2
	{
	SHA_LONG h0,h1,h2,h3,h4;
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
	} SHA_CTX2;

int SHA1_Init(SHA_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA1_Init2(SHA_CTX2 *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA1_Update(SHA_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA1_Update2(SHA_CTX2 *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA1_Final(void *md, SHA_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range((uint8_t *)md, SHA_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA1))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

int SHA1_Final2(void *md, SHA_CTX2 *c)
    _(requires \wrapped(c))
    _(writes \array_range(md,SHA_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA1))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

typedef struct SHA224state_st
	{
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num,md_len;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
	} SHA224_CTX;

typedef struct SHA256state_st
    {
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num,md_len;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
	} SHA256_CTX;

int SHA224_Init(SHA224_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA224_Update(SHA224_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA224_Final(void *md, SHA224_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md, SHA224_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA224_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA224))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

int SHA256_Init(SHA256_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA256_Update(SHA256_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA256_Final(void *md, SHA256_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md, SHA256_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA256_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA256))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

#define SHA_LONG64 unsigned __int64
    #define SHA512_CBLOCK	(SHA_LBLOCK*8)

typedef struct SHA384state_st
    {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl,Nh;
    union {
        _(backing_member) uint8_t temp[10000] ;
        struct S1{SHA_LONG64  d[SHA_LBLOCK];}d1;
        struct S2{unsigned char p[SHA512_CBLOCK];}d2;
    } u;
    unsigned int num,md_len;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
    } SHA384_CTX;

typedef struct SHA512state_st
    {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl,Nh;
    union {
        _(backing_member) uint8_t temp[10000] ;
        struct S1{SHA_LONG64  d[SHA_LBLOCK];}d1;
        struct S2{unsigned char p[SHA512_CBLOCK];}d2;
    } u;
    unsigned int num,md_len;
    _(ghost Num val)
    _(invariant valid(val))
    //_(invariant val == hashState(\this))
    } SHA512_CTX;

int SHA384_Init(SHA384_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA384_Update(SHA384_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA384_Final(void *md, SHA384_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md, SHA384_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA384_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA384))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

int SHA512_Init(SHA512_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(_(uint8_t)0,0))
    _(decreases 0)
;

int SHA512_Update(SHA512_CTX *c, const void *data, size_t len)
    _(requires \wrapped(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA512_Final(void *md, SHA512_CTX *c)
    _(requires \wrapped(c))
    _(writes \array_range(_(uint8_t *)md, SHA512_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA512_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA512))
    _(ensures c->val == repeat((uint8_t)0,0))
    _(decreases 0)
;

_(ghost _(pure) Num hashDigest(Num state, uint8_t *input, size_t len)
    {
    return state/{.val = (\lambda \natural i; i<state.len? state.val[i] : (i>state.len && i<state.len+len? input[i-state.len] : (uint8_t)0)),.len = state.len+len};
    })

typedef _(dynamic_owns) struct s2n_hash_state {
    s2n_hash_algorithm alg;
    union {
        MD5_CTX md5;
        SHA_CTX  sha1;
        SHA224_CTX sha224;
        SHA256_CTX sha256;
        SHA384_CTX sha384;
        SHA512_CTX sha512;
        struct {
            MD5_CTX2 md5;
            SHA_CTX2 sha1;
        }  md5_sha1;
    } hash_ctx;
    _(invariant alg >= 0 && alg <= 7)
    _(invariant alg == S2N_HASH_MD5 ==> \union_active(&hash_ctx.md5) && \mine(&hash_ctx.md5))
    _(invariant alg == S2N_HASH_SHA1 ==> \union_active(&hash_ctx.sha1) && \mine(&hash_ctx.sha1))
    _(invariant alg == S2N_HASH_SHA224 ==> \union_active(&hash_ctx.sha224) && \mine(&hash_ctx.sha224))
    _(invariant alg == S2N_HASH_SHA256 ==> \union_active(&hash_ctx.sha256) && \mine(&hash_ctx.sha256))
    _(invariant alg == S2N_HASH_SHA384 ==> \union_active(&hash_ctx.sha384) && \mine(&hash_ctx.sha384))
    _(invariant alg == S2N_HASH_SHA512 ==> \union_active(&hash_ctx.sha512) && \mine(&hash_ctx.sha512))
    _(invariant alg == S2N_HASH_MD5_SHA1 ==> \union_active(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1.sha1) && \mine(&hash_ctx.md5_sha1.md5))
    _(invariant \mine(&hash_ctx))
};

int hash_state_destroy(struct s2n_hash_state *s)
    _(requires \wrapped(s))
    _(writes s)
    _(ensures \extent_fresh(s))
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
    _(ensures s->alg == S2N_HASH_MD5 ==> \unchanged((&s->hash_ctx.md5)->val))
    _(ensures s->alg == S2N_HASH_SHA1 ==> \unchanged((&s->hash_ctx.sha1)->val))
    _(ensures s->alg == S2N_HASH_SHA224 ==> \unchanged((&s->hash_ctx.sha224)->val))
    _(ensures s->alg == S2N_HASH_SHA256 ==> \unchanged((&s->hash_ctx.sha256)->val))
    _(ensures s->alg == S2N_HASH_SHA384 ==> \unchanged((&s->hash_ctx.sha384)->val))
    _(ensures s->alg == S2N_HASH_SHA512 ==> \unchanged((&s->hash_ctx.sha512)->val))
    _(ensures s->alg == S2N_HASH_MD5_SHA1 ==> \unchanged((&s->hash_ctx.md5_sha1.md5)->val) && \unchanged((&s->hash_ctx.md5_sha1.sha1)->val))
    _(ensures s->alg == S2N_HASH_MD5 ==> valid((&s->hash_ctx.md5)->val) && \union_active(&s->hash_ctx.md5))
    _(ensures s->alg == S2N_HASH_SHA1 ==> valid((&s->hash_ctx.sha1)->val) && \union_active(&s->hash_ctx.sha1))
    _(ensures s->alg == S2N_HASH_SHA224 ==> valid((&s->hash_ctx.sha224)->val) && \union_active(&s->hash_ctx.sha224))
    _(ensures s->alg == S2N_HASH_SHA256 ==> valid((&s->hash_ctx.sha256)->val) && \union_active(&s->hash_ctx.sha256))
    _(ensures s->alg == S2N_HASH_SHA384 ==> valid((&s->hash_ctx.sha384)->val) && \union_active(&s->hash_ctx.sha384))
    _(ensures s->alg == S2N_HASH_SHA512 ==> valid((&s->hash_ctx.sha512)->val) && \union_active(&s->hash_ctx.sha512))
    _(ensures s->alg == S2N_HASH_MD5_SHA1 ==> valid((&s->hash_ctx.md5_sha1.md5)->val) && valid((&s->hash_ctx.md5_sha1.sha1)->val) && \union_active(&s->hash_ctx.md5_sha1))
    _(decreases 0)
;

int make_state_extent_mutable(struct s2n_hash_state *s)
    _(requires \wrapped(s))
    _(writes s)
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
;

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

_(def uint32_t alg_digest_size(s2n_hash_algorithm alg) 
{ 
    if (alg == S2N_HASH_NONE) return 0; 
    else if (alg == S2N_HASH_MD5) return MD5_DIGEST_LENGTH; 
    else if (alg == S2N_HASH_SHA1) return SHA_DIGEST_LENGTH; 
    else if (alg == S2N_HASH_SHA224) return SHA224_DIGEST_LENGTH; 
    else if (alg == S2N_HASH_SHA256) return SHA256_DIGEST_LENGTH; 
    else if (alg == S2N_HASH_SHA384) return SHA384_DIGEST_LENGTH;
    else if (alg == S2N_HASH_SHA512) return SHA512_DIGEST_LENGTH; 
    else if (alg == S2N_HASH_MD5_SHA1) return MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH; 
    else return 0;
})

    //Z PROBLEM HERE - THERE ISN'T JUST ONE TYPE OF CTX.
_(def Num hashState(struct s2n_hash_state *s, int a) { 
    if (s->alg == S2N_HASH_NONE) return repeat((uint8_t)0,0); 
    else if (s->alg == S2N_HASH_MD5) return (&s->hash_ctx.md5)->val; 
    else if (s->alg == S2N_HASH_SHA1) return (&s->hash_ctx.sha1)->val; 
    else if (s->alg == S2N_HASH_SHA224) return (&s->hash_ctx.sha224)->val; 
    else if (s->alg == S2N_HASH_SHA256) return (&s->hash_ctx.sha256)->val; 
    else if (s->alg == S2N_HASH_SHA384) return (&s->hash_ctx.sha384)->val;
    else if (s->alg == S2N_HASH_SHA512) return (&s->hash_ctx.sha512)->val; 
    else if (s->alg == S2N_HASH_MD5_SHA1 && !a) return (&s->hash_ctx.md5_sha1.md5)->val; 
    else if (s->alg == S2N_HASH_MD5_SHA1 &&  a) return (&s->hash_ctx.md5_sha1.sha1)->val; 
    else return repeat((uint8_t)0,0);
})

extern int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
    _(requires alg>= 0 && alg <= 7)
    _(requires \extent_mutable(state))
    _(writes \extent(state))
    _(ensures state->alg == alg)
    _(ensures \wrapped(state))
    _(ensures \result <= 0)
    //z TO WRITE PROPERLY _(ensures hashinit(alg) == hashstate(state->ctx))
    _(ensures !\result ==> &state->hash_ctx \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_MD5 ==> &state->hash_ctx.md5 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_SHA1 ==> &state->hash_ctx.sha1 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_SHA224 ==> &state->hash_ctx.sha224 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_SHA256 ==> &state->hash_ctx.sha256 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_SHA384 ==> &state->hash_ctx.sha384 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_SHA512 ==> &state->hash_ctx.sha512 \in state->\owns)
    _(ensures !\result && alg == S2N_HASH_MD5_SHA1 ==> &state->hash_ctx.md5_sha1 \in state->\owns &&
        &state->hash_ctx.md5_sha1.sha1 \in state->\owns &&
        &state->hash_ctx.md5_sha1.md5 \in state->\owns)
    _(ensures hashState(state,0) == repeat((uint8_t)0,0))
    _(ensures alg == S2N_HASH_MD5_SHA1 ==> hashState(state,1) == repeat((uint8_t)0,0))
    _(decreases 0)
;

int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
{
    int r;
    switch (alg) {
    case S2N_HASH_NONE:
        r = 1;
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx})
    break;
    case S2N_HASH_MD5:
        _(union_reinterpret &state->hash_ctx.md5)
        r = MD5_Init(&state->hash_ctx.md5);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.md5, &state->hash_ctx})
    break;
    case S2N_HASH_SHA1:
        _(union_reinterpret &state->hash_ctx.sha1)
        r = SHA1_Init(&state->hash_ctx.sha1);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha1, &state->hash_ctx})
    break;
    case S2N_HASH_SHA224:
        _(union_reinterpret &state->hash_ctx.sha224)
        r = SHA224_Init(&state->hash_ctx.sha224);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha224, &state->hash_ctx})
    break;
    case S2N_HASH_SHA256:
        _(union_reinterpret &state->hash_ctx.sha256)
        r = SHA256_Init(&state->hash_ctx.sha256);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha256, &state->hash_ctx})
    break;
    case S2N_HASH_SHA384:
        _(union_reinterpret &state->hash_ctx.sha384)
        r = SHA384_Init(&state->hash_ctx.sha384);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha384, &state->hash_ctx})
    break;
    case S2N_HASH_SHA512:
        _(union_reinterpret &state->hash_ctx.sha512)
        r = SHA512_Init(&state->hash_ctx.sha512);
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.sha512, &state->hash_ctx})
    break;
    case S2N_HASH_MD5_SHA1:
        _(union_reinterpret &state->hash_ctx.md5_sha1)
        r = SHA1_Init2(&state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Init2(&state->hash_ctx.md5_sha1.md5);
        _(wrap &state->hash_ctx.md5_sha1)
        _(wrap &state->hash_ctx)
        _(ghost state->\owns = {&state->hash_ctx.md5_sha1, &state->hash_ctx.md5_sha1.sha1, &state->hash_ctx.md5_sha1.md5, &state->hash_ctx})
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        _(assert 0)
    }
    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        _(assert 0)
    }
    state->alg = alg;
    _(wrap state)
    return 0;
}

extern int s2n_hash_update(struct s2n_hash_state *state, const void *in, uint32_t size)
    _(requires \wrapped(state))
    _(requires state->alg <= 6)
    _(writes state)
    _(ensures \result <= 0)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures state->alg ==> hashState(state,0) == concatenate(\old(hashState(state,0)),make_num((uint8_t *)in,size)))
    _(ensures state->alg == S2N_HASH_MD5_SHA1 ==> hashState(state,1) == concatenate(\old(hashState(state,1)),make_num((uint8_t *)in,size)))
    _(decreases 0)
;

int s2n_hash_update(struct s2n_hash_state *state, const void *data, uint32_t size)
{
    int r;
    _(unwrap state)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        r = MD5_Update(&state->hash_ctx.md5, data, size);
        break;
    case S2N_HASH_SHA1:
        r = SHA1_Update(&state->hash_ctx.sha1, data, size);
        break;
    case S2N_HASH_SHA224:
        r = SHA224_Update(&state->hash_ctx.sha224, data, size);
        break;
    case S2N_HASH_SHA256:
        r = SHA256_Update(&state->hash_ctx.sha256, data, size);
        break;
    case S2N_HASH_SHA384:
        r = SHA384_Update(&state->hash_ctx.sha384, data, size);
        break;
    case S2N_HASH_SHA512:
        r = SHA512_Update(&state->hash_ctx.sha512, data, size);
        break;
    case S2N_HASH_MD5_SHA1:
        _(unwrap &state->hash_ctx.md5_sha1)
        _(assert \wrapped(&state->hash_ctx.md5_sha1.md5))
        _(assert \wrapped(&state->hash_ctx.md5_sha1.sha1))
        r = MD5_Update2(&state->hash_ctx.md5_sha1.md5, data, size);
        _(wrap &state->hash_ctx.md5_sha1)
        _(unwrap &state->hash_ctx.md5_sha1)
        r &= SHA1_Update2(&state->hash_ctx.md5_sha1.sha1, data, size);
        _(assert (&state->hash_ctx.md5_sha1.md5)->val == concatenate(\old((&state->hash_ctx.md5_sha1.md5)->val),make_num((uint8_t *)data,size)))
        _(wrap &state->hash_ctx.md5_sha1)
        //r &= MD5_Update2(&state->hash_ctx.md5_sha1.md5, data, size);
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        _(assert 0)
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        _(assert 0)
    }
    _(wrap state)
    return 0;
}

extern int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(state->alg))
    _(writes state, \array_range(_(uint8_t *)outt,size))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures state->alg>0 && state->alg<=6 ==> make_num((uint8_t *)outt,size) == hashVal(\old(hashState(state,0)),state->alg))
    _(ensures state->alg == S2N_HASH_MD5_SHA1 ==> make_num((uint8_t *)outt,size) == concatenate(hashVal(\old(hashState(state,0)),S2N_HASH_MD5),hashVal(\old(hashState(state,1)),S2N_HASH_SHA1)))
    _(ensures state->alg ==> hashState(state,0) == repeat((uint8_t)0,0))
    _(ensures state->alg == S2N_HASH_MD5_SHA1 ==> hashState(state,1) == repeat((uint8_t)0,0))
    _(decreases 0)
;

int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
{
    int r;
    _(unwrap state)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        //eq_check(size, MD5_DIGEST_LENGTH);
        _(assert size == MD5_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = MD5_Final(outt, &state->hash_ctx.md5);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA1:
        //eq_check(size, SHA_DIGEST_LENGTH);
        _(assert size == SHA_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = SHA1_Final(outt, &state->hash_ctx.sha1);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA224:
        //eq_check(size, SHA224_DIGEST_LENGTH);
        _(assert size == SHA224_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = SHA224_Final(outt, &state->hash_ctx.sha224);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA256:
        //eq_check(size, SHA256_DIGEST_LENGTH);
        _(assert size == SHA256_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = SHA256_Final(outt, &state->hash_ctx.sha256);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA384:
        //eq_check(size, SHA384_DIGEST_LENGTH);
        _(assert size == SHA384_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = SHA384_Final(outt, &state->hash_ctx.sha384);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA512:
        //eq_check(size, SHA512_DIGEST_LENGTH);
        _(assert size == SHA512_DIGEST_LENGTH)
        _(unwrap &state->hash_ctx)
        r = SHA512_Final(outt, &state->hash_ctx.sha512);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_MD5_SHA1:
        //eq_check(size, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH);
        _(assert size == MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH)
        r = SHA1_Final2(((uint8_t *) outt) + MD5_DIGEST_LENGTH, &state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Final2(outt, &state->hash_ctx.md5_sha1.md5);
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INVALID_ALGORITHM);
        _(assert 0)
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_DIGEST_FAILED);
        _(assert 0)
    }
    _(wrap state)
    return 0;
}

extern int s2n_hash_reset(struct s2n_hash_state *state)
    _(requires \wrapped(state))
    _(writes state)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures !\result ==> &state->hash_ctx \in state->\owns)
    _(ensures !\result ==> state->alg ==> hashState(state,0) == repeat((uint8_t)0,0))
    _(ensures !\result ==> state->alg == S2N_HASH_MD5_SHA1 ==> hashState(state,1) == repeat((uint8_t)0,0))
    _(ensures !\result && state->alg == S2N_HASH_MD5 ==> &state->hash_ctx.md5 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_SHA1 ==> &state->hash_ctx.sha1 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_SHA224 ==> &state->hash_ctx.sha224 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_SHA256 ==> &state->hash_ctx.sha256 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_SHA384 ==> &state->hash_ctx.sha384 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_SHA512 ==> &state->hash_ctx.sha512 \in state->\owns)
    _(ensures !\result && state->alg == S2N_HASH_MD5_SHA1 ==> &state->hash_ctx.md5_sha1 \in state->\owns &&
        &state->hash_ctx.md5_sha1.sha1 \in state->\owns &&
        &state->hash_ctx.md5_sha1.md5 \in state->\owns)
    _(ensures \result <= 0)
;

int s2n_hash_reset(struct s2n_hash_state *state)
{
    hash_state_destroy(state);
    return s2n_hash_init(state,state->alg);
}

extern int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
    _(requires \extent_mutable(to))
    _(requires to->alg >= 0 && to->alg <= 7)
    _(requires \wrapped(from))
    _(requires from != to)
    _(writes \extent(to),from)
    _(ensures !\result &&from->alg ==> hashState(to,0) == \old(hashState(from,0))) 
    _(ensures !\result && from->alg == S2N_HASH_MD5_SHA1 ==> hashState(to,1) == \old(hashState(from,1))) 
    _(ensures !\result ==> \wrapped(to))
    _(ensures \result <= 0)
; 

int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
{
    hash_state_destroy(from);
    _(assert sizeof(struct s2n_hash_state) ==> to != NULL)
    //memcpy/*_check*/(to, from, sizeof(struct s2n_hash_state));
    *to = *from; //USER ADDED 
    if(from->alg == S2N_HASH_NONE) {
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx})
    }
    else if(from->alg == S2N_HASH_MD5) {
        _(wrap &to->hash_ctx.md5)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.md5, &to->hash_ctx})
    }
    else if(from->alg == S2N_HASH_SHA1) {
        _(wrap &to->hash_ctx.sha1)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha1, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA224) {
        _(wrap &to->hash_ctx.sha224)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha224, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA256) {
        _(wrap &to->hash_ctx.sha256)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha256, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA384) {
        _(wrap &to->hash_ctx.sha384)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha384, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA512) { 
        _(wrap &to->hash_ctx.sha512)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha512, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_MD5_SHA1) {
        _(wrap &to->hash_ctx.md5_sha1.sha1)
        _(wrap &to->hash_ctx.md5_sha1.md5)
        _(wrap &to->hash_ctx.md5_sha1)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.md5_sha1, &to->hash_ctx.md5_sha1.sha1, &to->hash_ctx.md5_sha1.md5, &to->hash_ctx})}
    else {_(assert 0)}
    _(wrap to)
    return 0;
}
