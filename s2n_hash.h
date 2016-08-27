#include <vcc.h>
#include <stdint.h>
#include <stdio.h>
#include "num.h"
#include <stdlib.h>

typedef enum { S2N_HASH_NONE, S2N_HASH_MD5, S2N_HASH_SHA1, S2N_HASH_SHA224, S2N_HASH_SHA256, S2N_HASH_SHA384,
    S2N_HASH_SHA512, S2N_HASH_MD5_SHA1
} s2n_hash_algorithm; 

_(def \bool is_valid_hash(s2n_hash_algorithm alg)
{
    if (alg>=0 && alg<=7) return 1;
    else return 0; 
})

_(ghost _(pure) Num hashVal(Num state, s2n_hash_algorithm alg)
  _(ensures \result.len == alg_digest_size(alg))
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
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} MD5_CTX;

typedef struct MD5state_st2
	{
	MD5_LONG A,B,C,D;
	MD5_LONG Nl,Nh;
	MD5_LONG data[MD5_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} MD5_CTX2;

int MD5_Init(MD5_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int MD5_Init2(MD5_CTX2 *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int MD5_Update(MD5_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int MD5_Update2(MD5_CTX2 *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len) && !(data \in \domain(c)))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)) && !(data \in \domain(c)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int MD5_Final(void *md, MD5_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md, MD5_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, MD5_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_MD5))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

int MD5_Final2(void *md, MD5_CTX2 *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md,  MD5_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, MD5_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_MD5))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
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
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA_CTX;

typedef struct SHAstate_st2
	{
	SHA_LONG h0,h1,h2,h3,h4;
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA_CTX2;

int SHA1_Init(SHA_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA1_Init2(SHA_CTX2 *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA1_Update(SHA_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(writes c)
    _(ensures \wrapped(c)  && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA1_Update2(SHA_CTX2 *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c)&& \thread_local_array((uint8_t *)data,len) && !(data \in \domain(c)))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len) && !(data \in \domain(c)))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA1_Final(void *md, SHA_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range((uint8_t *)md, SHA_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA1))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

int SHA1_Final2(void *md, SHA_CTX2 *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(md,SHA_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA1))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

typedef struct SHA224state_st
	{
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num,md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA224_CTX;

typedef struct SHA256state_st
    {
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num,md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA256_CTX;

int SHA224_Init(SHA224_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA224_Update(SHA224_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA224_Final(void *md, SHA224_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md, SHA224_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA224_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA224))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

int SHA256_Init(SHA256_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA256_Update(SHA256_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA256_Final(void *md, SHA256_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md, SHA256_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA256_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA256))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
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
    _(ghost \bool valid)
    _(invariant valid_num(val))
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
    _(ghost \bool valid)
    _(invariant valid_num(val))
    } SHA512_CTX;

int SHA384_Init(SHA384_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA384_Update(SHA384_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA384_Final(void *md, SHA384_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md, SHA384_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA384_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA384))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

int SHA512_Init(SHA512_CTX *c)
    _(requires \mutable(c))
    _(writes c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures c->val == repeat(0x0,0))
    _(ensures c->valid)
    _(decreases 0)
;

int SHA512_Update(SHA512_CTX *c, const void *data, size_t len)
    _(maintains c->valid)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes c)
    _(ensures \wrapped(c) && \thread_local_array((uint8_t *)data,len))
    _(ensures \result == 1)
    _(ensures c->val == concatenate(\old(c->val),make_num((uint8_t *)data,len)))
    _(ensures \unchanged(make_num((uint8_t *)data,len)))
    _(decreases 0)
;

int SHA512_Final(void *md, SHA512_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes \array_range(_(uint8_t *)md, SHA512_DIGEST_LENGTH), c)
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA512_DIGEST_LENGTH) == hashVal(\old(c->val),S2N_HASH_SHA512))
    _(ensures c->val == repeat(0x0,0))
    _(ensures !c->valid)
    _(decreases 0)
;

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
    _(ghost \bool real)
    _(ghost Num hashState)
    _(invariant real ==> valid_num(hashState))
    _(ghost \bool valid)
    _(invariant real ==> is_valid_hash(alg))
    _(invariant real && alg == S2N_HASH_NONE ==> hashState == repeat(0x0,0))
    _(invariant real && alg == S2N_HASH_MD5 ==> \union_active(&hash_ctx.md5) && \mine(&hash_ctx.md5) && hashState == (&hash_ctx.md5)->val && valid == (&hash_ctx.md5)->valid)
    _(invariant real && alg == S2N_HASH_SHA1 ==> \union_active(&hash_ctx.sha1) && \mine(&hash_ctx.sha1) && hashState == (&hash_ctx.sha1)->val && valid == (&hash_ctx.sha1)->valid)
    _(invariant real && alg == S2N_HASH_SHA224 ==> \union_active(&hash_ctx.sha224) && \mine(&hash_ctx.sha224) && hashState == (&hash_ctx.sha224)->val && valid == (&hash_ctx.sha224)->valid)
    _(invariant real && alg == S2N_HASH_SHA256 ==> \union_active(&hash_ctx.sha256) && \mine(&hash_ctx.sha256) && hashState == (&hash_ctx.sha256)->val && valid == (&hash_ctx.sha256)->valid)
    _(invariant real && alg == S2N_HASH_SHA384 ==> \union_active(&hash_ctx.sha384) && \mine(&hash_ctx.sha384) && hashState == (&hash_ctx.sha384)->val && valid == (&hash_ctx.sha384)->valid)
    _(invariant real && alg == S2N_HASH_SHA512 ==> \union_active(&hash_ctx.sha512) && \mine(&hash_ctx.sha512) && hashState == (&hash_ctx.sha512)->val && valid == (&hash_ctx.sha512)->valid)
    _(invariant real && alg == S2N_HASH_MD5_SHA1 ==> \union_active(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1.sha1) && \mine(&hash_ctx.md5_sha1.md5) && hashState == (&hash_ctx.md5_sha1.md5)->val && hashState == (&hash_ctx.md5_sha1.sha1)->val && valid == (&hash_ctx.md5_sha1.md5)->valid && valid == (&hash_ctx.md5_sha1.sha1)->valid)
    _(invariant \mine(&hash_ctx))
};

#define wrap_hash_state(state) \
   if(state->alg == S2N_HASH_NONE) {\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx})\
    }\
    else if(state->alg == S2N_HASH_MD5) {\
        _(wrap &state->hash_ctx.md5)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.md5, &state->hash_ctx})\
    }\
    else if(state->alg == S2N_HASH_SHA1) {\
        _(wrap &state->hash_ctx.sha1)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.sha1, &state->hash_ctx})}\
    else if(state->alg == S2N_HASH_SHA224) {\
        _(wrap &state->hash_ctx.sha224)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.sha224, &state->hash_ctx})}\
    else if(state->alg == S2N_HASH_SHA256) {\
        _(wrap &state->hash_ctx.sha256)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.sha256, &state->hash_ctx})}\
    else if(state->alg == S2N_HASH_SHA384) {\
        _(wrap &state->hash_ctx.sha384)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.sha384, &state->hash_ctx})}\
    else if(state->alg == S2N_HASH_SHA512) { \
        _(wrap &state->hash_ctx.sha512)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.sha512, &state->hash_ctx})}\
    else if(state->alg == S2N_HASH_MD5_SHA1) {\
        _(wrap &state->hash_ctx.md5_sha1.sha1)\
        _(wrap &state->hash_ctx.md5_sha1.md5)\
        _(wrap &state->hash_ctx.md5_sha1)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.md5_sha1, &state->hash_ctx.md5_sha1.sha1, &state->hash_ctx.md5_sha1.md5, &state->hash_ctx})}\
    else {_(assert 0)}

_(ghost int hash_state_destroy(struct s2n_hash_state *s)
    _(requires \wrapped(s))
    _(writes s)
    _(ensures \extent_fresh(s))
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
    _(ensures \unchanged(s->hashState))
    _(ensures \unchanged(s->valid))
    _(ensures s->alg == S2N_HASH_MD5 ==> \union_active(&s->hash_ctx.md5) && \unchanged((&s->hash_ctx.md5)->valid) && \unchanged((&s->hash_ctx.md5)->val))
    _(ensures s->alg == S2N_HASH_SHA1 ==> \union_active(&s->hash_ctx.sha1) && \unchanged((&s->hash_ctx.sha1)->valid) && \unchanged((&s->hash_ctx.sha1)->val))
    _(ensures s->alg == S2N_HASH_SHA224 ==> \union_active(&s->hash_ctx.sha224) && \unchanged((&s->hash_ctx.sha224)->valid) && \unchanged((&s->hash_ctx.sha224)->val))
    _(ensures s->alg == S2N_HASH_SHA256 ==> \union_active(&s->hash_ctx.sha256) && \unchanged((&s->hash_ctx.sha256)->valid) && \unchanged((&s->hash_ctx.sha256)->val))
    _(ensures s->alg == S2N_HASH_SHA384 ==> \union_active(&s->hash_ctx.sha384) && \unchanged((&s->hash_ctx.sha384)->valid) && \unchanged((&s->hash_ctx.sha384)->val))
    _(ensures s->alg == S2N_HASH_SHA512 ==> \union_active(&s->hash_ctx.sha512) && \unchanged((&s->hash_ctx.sha512)->valid) && \unchanged((&s->hash_ctx.sha512)->val))
    _(ensures s->alg == S2N_HASH_MD5_SHA1 ==> \union_active(&s->hash_ctx.md5_sha1) && \unchanged((&s->hash_ctx.md5_sha1.md5)->valid) && \unchanged((&s->hash_ctx.md5_sha1.sha1)->valid) && \unchanged((&s->hash_ctx.md5_sha1.md5)->val) && \unchanged((&s->hash_ctx.md5_sha1.sha1)->val))
    _(ensures \unchanged(s->real))
    _(decreases 0)
;)

extern int s2n_hash_digest_size(s2n_hash_algorithm alg)
    _(requires is_valid_hash(alg))
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

_(def Num hashState(struct s2n_hash_state *s, int a) { 
    if (s->alg == S2N_HASH_NONE) return repeat(0x0,0); 
    else if (s->alg == S2N_HASH_MD5) return (&s->hash_ctx.md5)->val; 
    else if (s->alg == S2N_HASH_SHA1) return (&s->hash_ctx.sha1)->val; 
    else if (s->alg == S2N_HASH_SHA224) return (&s->hash_ctx.sha224)->val; 
    else if (s->alg == S2N_HASH_SHA256) return (&s->hash_ctx.sha256)->val; 
    else if (s->alg == S2N_HASH_SHA384) return (&s->hash_ctx.sha384)->val;
    else if (s->alg == S2N_HASH_SHA512) return (&s->hash_ctx.sha512)->val; 
    else if (s->alg == S2N_HASH_MD5_SHA1 && !a) return (&s->hash_ctx.md5_sha1.md5)->val; 
    else if (s->alg == S2N_HASH_MD5_SHA1 &&  a) return (&s->hash_ctx.md5_sha1.sha1)->val; 
    else return repeat(0x0,0);
})

extern int s2n_hash_init_none(struct s2n_hash_state *state, s2n_hash_algorithm alg)
    _(requires is_valid_hash(alg))
    _(writes \extent(state))
    _(ensures \wrapped(state))
    _(ensures state->alg == alg)
    _(ensures \result == 0)
    _(ensures state->hashState == repeat(0x0,0))
    _(ensures !state->valid)
    _(decreases 0)
;

extern int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
    _(requires is_valid_hash(alg))
    _(writes \extent(state))
    _(ensures \wrapped(state))
    _(ensures state->alg == alg)
    _(ensures \result == 0)
    _(ensures state->hashState == repeat(0x0,0))
    _(ensures state->valid)
    _(ensures state->real)
    _(decreases 0)
;

extern int s2n_hash_update(struct s2n_hash_state *state, const void *in, uint32_t size)
    _(maintains state->valid)
    _(maintains \wrapped(state))
    _(requires \thread_local_array((uint8_t*)in,size))
    _(maintains !(in \in \domain(state))) //IS REQUIRES ENOUGH?
    _(writes state)
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(make_num((uint8_t*)in,size)))
    _(ensures state->alg ==> state->hashState == concatenate(\old(state->hashState),make_num((uint8_t *)in,size)))
    _(ensures !state->alg ==> \unchanged(state->hashState))
    _(ensures \result == 0)
    _(maintains state->real)
    _(decreases 0)
;

extern int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(state->alg))
    _(requires state->valid)
    _(writes state, \array_range(_(uint8_t *)outt,size))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures state->alg && state->alg != S2N_HASH_MD5_SHA1 ==> make_num((uint8_t *)outt,size) == hashVal(\old(state->hashState),state->alg))
    _(ensures state->alg == S2N_HASH_MD5_SHA1 ==> make_num((uint8_t *)outt,size) == concatenate(hashVal(\old(state->hashState),S2N_HASH_MD5),hashVal(\old(state->hashState),S2N_HASH_SHA1)))
    _(ensures state->hashState == repeat(0x0,0))
    _(ensures !state->alg ==> make_num((uint8_t *)outt,size) == \old(make_num((uint8_t *)outt,size)))
    _(ensures !state->valid)
    _(ensures \result == 0)
    _(maintains state->real)
    _(decreases 0)
;

extern int s2n_hash_reset(struct s2n_hash_state *state)
    _(requires \wrapped(state))
    _(writes state)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures state->valid)
    _(ensures state->hashState == repeat(0x0,0))
    _(ensures \result == 0)
    _(maintains state->real)
;

extern int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
    _(requires \extent_mutable(to))
    _(requires \wrapped(from))
    _(requires from != to)
    _(requires from->valid)
    _(writes \extent(to),from)
    _(ensures to->hashState == from->hashState)
    _(ensures !\result ==> \wrapped(to))
    _(ensures to->valid)
    _(requires from->real)
    _(ensures to->real)
    _(ensures \result <= 0)
; 

