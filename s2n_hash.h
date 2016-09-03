#include "num.h"
#include <stdlib.h>

#define myInv(algo, cmp)    valid && alg == S2N_HASH_ ## algo ==> \union_active(&hash_ctx. ## cmp) \
    && \mine(&hash_ctx. ## cmp) && hashState == (&hash_ctx. ## cmp)->val && valid == (&hash_ctx. ## cmp)->valid

#define my2Inv(algo, cmp) valid && alg == S2N_HASH_ ## algo ==> \union_active(&hash_ctx.## cmp) && \mine(&hash_ctx. ## cmp) && \
    \mine(&hash_ctx. ## cmp ##.sha1) && \mine(&hash_ctx. ## cmp ##.md5) && hashState == (&hash_ctx. ## cmp ## .md5)->val && \
    hashState == (&hash_ctx. ## cmp ## .sha1)->val && valid == (&hash_ctx. ## cmp ## .md5)->valid && valid == \
    (&hash_ctx. ## cmp ## .sha1)->valid

/*The main object used in this file is the struct s2n_hash_state. s2n_hash_state has a concrete field `alg' which keeps track of the hash algorithm being used (which can be MD5, SHA1, SHA224, SHA256, SHA384 or SHA512), and a concrete field called `hash_ctx', which is a union of various structs called `contexts' which are used by OpenSSL functions.*/

typedef enum { S2N_HASH_NONE, S2N_HASH_MD5, S2N_HASH_SHA1, S2N_HASH_SHA224, S2N_HASH_SHA256, S2N_HASH_SHA384,
    S2N_HASH_SHA512, S2N_HASH_MD5_SHA1
} s2n_hash_algorithm; 

_(def \bool is_valid_hash(s2n_hash_algorithm alg)
{
    return(alg>=0 && alg<=7); 
})

/*This will be used in s2n_hash_digest. To keep track of what's happened to the string we've hashed the context onto, we use the function `hashVal'. */
_(ghost _(pure) Num hashVal(Num n, s2n_hash_algorithm alg)
  _(ensures \result.len == alg_digest_size(alg))
  _(ensures \result == concatenate(hashVal(n, S2N_HASH_MD5), hashVal(n, S2N_HASH_SHA1)))
  _(decreases 0))

/*To each context we add a ghost Num field `val' which stores the abstract value of that context, and a ghost boolean field `valid' that indicates whether it's valid or whether it needs to be reset before being used.*/
#define MD5_LONG unsigned int
#define MD5_CBLOCK	64
#define MD5_LBLOCK	(MD5_CBLOCK/4)
#define MD5_DIGEST_LENGTH 16
typedef struct MD5state_st {
    MD5_LONG A,B,C,D;
    MD5_LONG Nl,Nh;
    MD5_LONG data[MD5_LBLOCK];
    unsigned int num;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
    } MD5_CTX;

#define init_contract     \
    _(requires \mutable(c))\
    _(writes c)\
    _(ensures \wrapped(c))\
    _(ensures \result == 1)\
    _(ensures c->val == repeat(0x0, 0))\
    _(ensures c->valid)\
    _(decreases 0)

#define update_contract \
    _(maintains c->valid)\
    _(requires \thread_local_array((uint8_t*)data, len))\
    _(maintains \wrapped(c))\
    _(writes c)\
    _(ensures \wrapped(c))\
    _(ensures \result == 1)\
    _(ensures c->val == concatenate(\old(c->val), make_num((uint8_t *)data, len)))\
    _(decreases 0)

#define final_contract(alg) \
    _(maintains \wrapped(c))\
    _(requires c->valid)\
    _(writes c, \array_range(_(uint8_t *)md, alg ## _DIGEST_LENGTH))\
    _(ensures \result == 1)\
    _(ensures make_num((uint8_t *)md, alg ## _DIGEST_LENGTH) == hashVal(\old(c->val), S2N_HASH_ ## alg))\
    _(decreases 0)

/*initialises a context, which we keep track of by setting its valid flag to 1, setting its abstract value to a Num of length zero, and wrapping it; */
int MD5_Init(MD5_CTX *c)
    init_contract
;

/* takes a valid, wrapped context and appends some data, which we keep track of by appending that data to the context's abstract value. As we keep the context valid and wrapped, we note that this function can be called repeatedly*/
int MD5_Update(MD5_CTX *c, const void *data, size_t len)
    update_contract
;

int MD5_Final(void *md, MD5_CTX *c)
    final_contract(MD5)
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
	SHA_LONG h0, h1 ,h2 ,h3, h4;
	SHA_LONG Nl, Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA_CTX;

int SHA1_Init(SHA_CTX *c)
    init_contract
;

int SHA1_Update(SHA_CTX *c, const void *data, size_t len)
    update_contract
;

int SHA1_Final(void *md, SHA_CTX *c)
    _(requires \wrapped(c))
    _(requires c->valid)
    _(writes c, \array_range(_(uint8_t *)md, SHA_DIGEST_LENGTH))
    _(ensures \wrapped(c))
    _(ensures \result == 1)
    _(ensures make_num((uint8_t *)md, SHA_DIGEST_LENGTH) == hashVal(\old(c->val), S2N_HASH_SHA1))
    _(decreases 0)
;

typedef struct SHA224state_st
	{
	SHA_LONG h[8];
	SHA_LONG Nl, Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num, md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA224_CTX;

typedef struct SHA256state_st
    {
	SHA_LONG h[8];
	SHA_LONG Nl, Nh;
	SHA_LONG data[SHA_LBLOCK];
	unsigned int num, md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
	} SHA256_CTX;

int SHA224_Init(SHA224_CTX *c)
    init_contract
;

int SHA224_Update(SHA224_CTX *c, const void *data, size_t len)
    update_contract
;

int SHA224_Final(void *md, SHA224_CTX *c)
    final_contract(SHA224)

;

int SHA256_Init(SHA256_CTX *c)
    init_contract
;

int SHA256_Update(SHA256_CTX *c, const void *data, size_t len)
    update_contract
;

int SHA256_Final(void *md, SHA256_CTX *c)
    final_contract(SHA256)
;

#define SHA_LONG64 unsigned __int64
    #define SHA512_CBLOCK	(SHA_LBLOCK*8)

typedef struct SHA384state_st
    {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl, Nh;
    union {
        _(backing_member) uint8_t temp[10000] ;
        struct S1{SHA_LONG64  d[SHA_LBLOCK];}d1;
        struct S2{unsigned char p[SHA512_CBLOCK];}d2;
    } u;
    unsigned int num, md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
    } SHA384_CTX;

typedef struct SHA512state_st
    {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl, Nh;
    union {
        _(backing_member) uint8_t temp[10000] ;
        struct S1{SHA_LONG64  d[SHA_LBLOCK];}d1;
        struct S2{unsigned char p[SHA512_CBLOCK];}d2;
    } u;
    unsigned int num, md_len;
    _(ghost Num val)
    _(ghost \bool valid)
    _(invariant valid_num(val))
    } SHA512_CTX;

int SHA384_Init(SHA384_CTX *c)
    init_contract
;

int SHA384_Update(SHA384_CTX *c, const void *data, size_t len)
    update_contract
;

int SHA384_Final(void *md, SHA384_CTX *c)
    final_contract(SHA384)
;

int SHA512_Init(SHA512_CTX *c)
    init_contract
;

int SHA512_Update(SHA512_CTX *c, const void *data, size_t len)
    update_contract
;

int SHA512_Final(void *md, SHA512_CTX *c)
    final_contract(SHA512)
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
            MD5_CTX md5;
            SHA_CTX sha1;
        }  md5_sha1;
    } hash_ctx;
    _(ghost Num hashState)
    _(invariant valid ==> valid_num(hashState))
    _(ghost \bool valid)
    _(invariant valid ==> is_valid_hash(alg))
    _(invariant myInv(MD5, md5))
    _(invariant myInv(SHA1, sha1))
    _(invariant myInv(SHA224, sha224))
    _(invariant myInv(SHA256, sha256))
    _(invariant myInv(SHA384, sha384))
    _(invariant myInv(SHA512, sha512))
    _(invariant valid && alg == S2N_HASH_MD5_SHA1 ==> \union_active(&hash_ctx.md5_sha1) && \mine(&hash_ctx.md5_sha1) && 
    \mine(&hash_ctx.md5_sha1.sha1) && \mine(&hash_ctx.md5_sha1.md5) && hashState == (&hash_ctx.md5_sha1.md5)->val && 
    hashState == (&hash_ctx.md5_sha1.sha1)->val && valid == (&hash_ctx.md5_sha1.md5)->valid && valid == 
    (&hash_ctx.md5_sha1.sha1)->valid)
    _(invariant \mine(&hash_ctx))
};

#define mywrap(state, alg)         _(wrap &state->hash_ctx. ## alg)\
    _(wrap &state->hash_ctx)\
    _(ghost state->\owns = {&state->hash_ctx. ## alg, &state->hash_ctx})}

#define wrap_hash_state(state) \
    {if(state->alg == S2N_HASH_NONE) {\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx})\
    }\
    else if(state->alg == S2N_HASH_MD5) {\
    mywrap(state, md5) \
    else if(state->alg == S2N_HASH_SHA1) {\
        mywrap(state, sha1) \
    else if(state->alg == S2N_HASH_SHA224) {\
        mywrap(state, sha224) \
    else if(state->alg == S2N_HASH_SHA256) {\
        mywrap(state, sha256) \
    else if(state->alg == S2N_HASH_SHA384) {\
        mywrap(state, sha384) \
    else if(state->alg == S2N_HASH_SHA512) { \
        mywrap(state, sha512) \
    else if(state->alg == S2N_HASH_MD5_SHA1) {\
         _(wrap &state->hash_ctx.md5_sha1.sha1)\
        _(wrap &state->hash_ctx.md5_sha1.md5)\
        _(wrap &state->hash_ctx.md5_sha1)\
        _(wrap &state->hash_ctx)\
        _(ghost state->\owns = {&state->hash_ctx.md5_sha1, &state->hash_ctx.md5_sha1.sha1, \
            &state->hash_ctx.md5_sha1.md5, &state->hash_ctx})}\
    else {_(assert 0)};\
    _(wrap state);}

#define mypostcondition(s, alg) \union_active(& ## s ## ->hash_ctx.md5) && \unchanged((& ## s ## ->hash_ctx.md5)->valid) && \
    \unchanged((& ## s ## ->hash_ctx.md5)->val)

#define my2postcondition(s, alg) \union_active(& ## s ## ->hash_ctx. ## md5_sha1 ## ) && \unchanged((& ## s ## ->hash_ctx. ## md5_sha1 ## .md5)->valid) && \
    \unchanged((& ## s ## ->hash_ctx. ## md5_sha1 ## .sha1)->valid) && \unchanged((& ## s ## ->hash_ctx. ## md5_sha1 ## .md5)->val) && \unchanged((& ## s ## ->hash_ctx. ## md5_sha1 ## .sha1)->val)

_(ghost int hash_state_destroy(struct s2n_hash_state *s)
    _(requires \wrapped(s))
    _(writes s)
    _(ensures \extent_fresh(s))
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
    _(ensures \unchanged(s->hashState))
    _(ensures \unchanged(s->valid))
    _(ensures s->alg == S2N_HASH_MD5 ==> mypostcondition(s, md5))
    _(ensures s->alg == S2N_HASH_SHA1 ==> mypostcondition(s, sha1))
    _(ensures s->alg == S2N_HASH_SHA224 ==> mypostcondition(s, sha224))
    _(ensures s->alg == S2N_HASH_SHA256 ==> mypostcondition(s, sha256))
    _(ensures s->alg == S2N_HASH_SHA384 ==> mypostcondition(s, sha384))
    _(ensures s->alg == S2N_HASH_SHA512 ==> mypostcondition(s, sha512))
    _(ensures s->alg == S2N_HASH_MD5_SHA1 ==> \union_active(&s->hash_ctx.md5_sha1) && 
        \unchanged((&s->hash_ctx.md5_sha1.md5)->valid) && \unchanged((&s->hash_ctx.md5_sha1.sha1)->valid) && 
        \unchanged((&s->hash_ctx.md5_sha1.md5)->val) && \unchanged((&s->hash_ctx.md5_sha1.sha1)->val))
    _(decreases 0)
;)

extern int s2n_hash_digest_size(s2n_hash_algorithm alg)
    _(requires is_valid_hash(alg))
    _(ensures \result == (int)(alg_digest_size(alg)))
;

int s2n_hash_digest_size(s2n_hash_algorithm alg)
{
    int sizes[] = { 0, MD5_DIGEST_LENGTH, SHA_DIGEST_LENGTH, SHA224_DIGEST_LENGTH, SHA256_DIGEST_LENGTH, 
        SHA384_DIGEST_LENGTH, SHA512_DIGEST_LENGTH, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH };

    return sizes[alg];
}

#define mycomm(in) if (alg == S2N_HASH_ ## in) return in ## _DIGEST_LENGTH

_(def uint32_t alg_digest_size(s2n_hash_algorithm alg) 
{ 
    if (alg == S2N_HASH_NONE) return 0; 
    else mycomm(MD5); 
    else if (alg == S2N_HASH_SHA1) return SHA_DIGEST_LENGTH; 
    else mycomm(SHA224); 
    else mycomm(SHA256); 
    else mycomm(SHA384);
    else mycomm(SHA512); 
    else if (alg == S2N_HASH_MD5_SHA1) return MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH; 
    else return 0;
})

#undef mycomm

#define WRAPPED_VALID(state) \wrapped( ## state ## ) && state ## ->valid

extern int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
    _(requires is_valid_hash(alg))
    _(writes \extent(state))
    _(ensures WRAPPED_VALID(state))
    _(ensures state->alg == alg)
    _(ensures \result == 0)
    _(ensures state->hashState == repeat(0x0,0))
    _(decreases 0)
;

extern int s2n_hash_update(struct s2n_hash_state *state, const void *in, uint32_t size)
    _(maintains WRAPPED_VALID(state))
    _(requires \thread_local_array((uint8_t*)in, size))
    _(requires !(\domain_root(\embedding((uint8_t *)in)) \in \domain(state)))
    _(writes state)
    _(ensures \unchanged(state->alg))
    _(ensures state->hashState == concatenate(\old(state->hashState), make_num((uint8_t *)in, size)))
    _(ensures \result == 0)
    _(decreases 0)
;

extern int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires size == alg_digest_size(state->alg))
    _(writes state, \array_range(_(uint8_t *)outt, size))
    _(ensures \result == 0)
    _(ensures \unchanged(state->alg))
    _(ensures \wrapped(state))
    _(ensures make_num((uint8_t *)outt, size) == hashVal(\old(state->hashState), state->alg))
    _(ensures state->hashState == repeat(0x0, 0))
    _(ensures \result == 0)
    _(decreases 0)
;

extern int s2n_hash_reset(struct s2n_hash_state *state)
    _(requires \wrapped(state))
    _(requires is_valid_hash(state->alg))
    _(writes state)
    _(ensures \unchanged(state->alg))
    _(ensures WRAPPED_VALID(state))
    _(ensures state->hashState == repeat(0x0, 0))
    _(ensures \result == 0)
;

extern int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
    _(requires \extent_mutable(to))
    _(maintains WRAPPED_VALID(from))
    _(requires from != to)
    _(writes \extent(to), from)
    _(ensures \unchanged(from->hashState))
    _(ensures to->hashState == from->hashState)
    _(ensures WRAPPED_VALID(to))
    _(ensures \result == 0)
; 

