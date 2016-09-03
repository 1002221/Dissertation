/*
 * Copyright 2014 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#pragma once

#include "s2n_hash.h"
#include "s2n_safety.h"

#define IPAD repeat(0x36,state->block_size)
#define OPAD repeat(0x5c,state->block_size)
#define Kprime num_resize(state->key,state->block_size)
#define Kprime2 num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size)
#define H(NAME) hashVal(NAME ## ,hmac_to_hash(state->alg))
#define H1(NAME) hashVal(NAME ## ,hmac_to_hash(state->alg))
#define L state->block_size

#define _IPAD repeat(0x36,block_size)
#define _OPAD repeat(0x5c,block_size)
#define _Kprime num_resize(key,block_size)
#define _Kprime2 num_resize(hashVal(key,hmac_to_hash(alg)),block_size)
#define _L block_size

#define UNCHANGED_HMAC_ALG_KEY \unchanged(state->alg) && \unchanged(state->key)

typedef enum { S2N_HMAC_NONE, S2N_HMAC_MD5, S2N_HMAC_SHA1, S2N_HMAC_SHA224, S2N_HMAC_SHA256, S2N_HMAC_SHA384,
    S2N_HMAC_SHA512, S2N_HMAC_SSLv3_MD5, S2N_HMAC_SSLv3_SHA1
} s2n_hmac_algorithm;

struct s2n_hmac_state {
    s2n_hmac_algorithm alg;

    uint16_t hash_block_size;
    _(invariant hash_block_size == hash_block_size_alg(alg))
    uint32_t currently_in_hash_block;
    uint16_t block_size;
    _(invariant _L == block_size_alg(alg))
    uint8_t digest_size;
    _(invariant digest_size == digest_size_alg(alg))

    _(ghost Num key)
    _(invariant valid_num(key))

    _(ghost \bool valid)
    _(invariant valid ==> (&inner)->valid)
    _(invariant (&inner_just_key)->valid)
    _(invariant is_sslv3(alg) ==> (&outer)->valid)

    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;
    
    _(ghost Num message)
    _(invariant valid ==> valid_num(message))
    _(invariant valid ==> concatenate((&inner_just_key)->hashState, message) == (&inner)->hashState)
    
    _(invariant key.len <= block_size && !is_sslv3(alg)  ==> (&inner_just_key)->hashState == xor(_Kprime,_IPAD))
    _(invariant key.len > block_size && !is_sslv3(alg)  ==> (&inner_just_key)->hashState == xor(_Kprime2,_IPAD))
    //_(invariant !alg ==> (&inner_just_key)->hashState == repeat(0x0,0))
    _(invariant !is_sslv3(alg)  ==> (&outer)->hashState == repeat(0x0,0))
    _(invariant is_sslv3(alg)   ==> (&inner_just_key)->hashState == concatenate(key,_IPAD))
    _(invariant is_sslv3(alg) ==> (&outer)->hashState == concatenate(key,_OPAD))
    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];
    _(invariant key.len>_L && alg && !is_sslv3(alg) ==> make_num(xor_pad,_L) == xor(_Kprime2,_OPAD))
    _(invariant key.len>_L && !alg && !is_sslv3(alg) ==> make_num(xor_pad,_L) == _OPAD)
    _(invariant key.len<=_L && !is_sslv3(alg) ==> make_num(xor_pad,_L) == xor(_Kprime,_OPAD))
    _(invariant is_sslv3(alg) ==> make_num(xor_pad,_L) == _OPAD)
    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
    _(invariant alg>=0 && alg <= 8)
    _(invariant valid ==>(&inner)->alg == hmac_to_hash(alg))
    _(invariant (&inner_just_key)->alg == hmac_to_hash(alg))
    _(invariant (&outer)->alg == hmac_to_hash(alg))
    _(invariant \mine(&inner) && \mine(&outer) && \mine(&inner_just_key))
};

#define conditionalwrap(state,alg)\
    if((state)->valid){\
    _(wrap &(state)->hash_ctx. ## alg) \
        _(wrap &(state)->hash_ctx) \
        _(ghost (state)->\owns = {&(state)->hash_ctx. ## alg, &(state)->hash_ctx})} \
    else {\
        _(wrap &(state)->hash_ctx) \
        _(ghost (state)->\owns = {&(state)->hash_ctx})} \

#define wrap_inners(state,alg)\
    _(wrap &(&state->inner_just_key)->hash_ctx. ## alg) \
    _(wrap &(&state->inner_just_key)->hash_ctx) \
    _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx. ## alg, &(&state->inner_just_key)->hash_ctx}) \
    _(wrap &(&state->inner)->hash_ctx. ## alg) \
    _(wrap &(&state->inner)->hash_ctx) \
    _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx. ## alg, &(&state->inner)->hash_ctx}) \

#define wrap_none(state)\
    _(wrap &(state)->hash_ctx) \
        _(ghost (state)->\owns = {&(state)->hash_ctx}) \

#define wrap_hmac_state(state) {switch(hmac_to_hash(state->alg)){ \
    case S2N_HASH_NONE: \
        wrap_none((&state->inner)) \
        wrap_none((&state->inner_just_key)) \
        wrap_none((&state->outer)) \
    break; \
    case S2N_HASH_MD5: \
        wrap_inners(state,md5)\
        conditionalwrap((&state->outer),md5)\
        break; \
    case S2N_HASH_SHA1: \
        wrap_inners(state,sha1)\
        conditionalwrap((&state->outer),sha1)\
    break; \
    case S2N_HASH_SHA224: \
        wrap_inners(state,sha224)\
        conditionalwrap((&state->outer),sha224)\
    break; \
    case S2N_HASH_SHA256: \
        wrap_inners(state,sha256)\
        conditionalwrap((&state->outer),sha256)\
    break; \
    case S2N_HASH_SHA384: \
        wrap_inners(state,sha384)\
        conditionalwrap((&state->outer),sha384)\
    break; \
    case S2N_HASH_SHA512: \
        wrap_inners(state,sha512)\
        conditionalwrap((&state->outer),sha512)\
    break; \
    default: _(assert 0)} \
    _(wrap &state->inner_just_key) \
    _(wrap &state->inner) \
    _(wrap &state->outer) \
    _(ghost state->\owns = {&state->inner_just_key, &state->inner, &state->outer}) \
    _(wrap state)}

extern int s2n_hmac_digest_size(s2n_hmac_algorithm alg)
    _(requires alg >= 0 && alg <= 8)
;

_(def uint16_t block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE || alg == S2N_HMAC_SHA224 || alg == S2N_HMAC_SHA256) return 64; 
    if (alg == S2N_HMAC_MD5 || alg == S2N_HMAC_SSLv3_MD5) return 48; 
    if (alg == S2N_HMAC_SHA1 || alg == S2N_HMAC_SSLv3_SHA1) return 40; 
    if (alg == S2N_HMAC_SHA384 || alg == S2N_HMAC_SHA512) return 128; 
    else return 64; 
})

_(def uint16_t hash_block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE || alg == S2N_HMAC_MD5 || alg == S2N_HMAC_SHA1 || alg == S2N_HMAC_SHA224 || alg == S2N_HMAC_SHA256 || 
        alg == S2N_HMAC_SSLv3_MD5 || alg == S2N_HMAC_SSLv3_SHA1) return 64; 
    if (alg == S2N_HMAC_SHA384 || alg == S2N_HMAC_SHA512) return 128; 
    else return 64; 
})

_(def uint16_t digest_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE) return 0; 
    if (alg == S2N_HMAC_MD5 || alg == S2N_HMAC_SSLv3_MD5) return MD5_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA1 || alg == S2N_HMAC_SSLv3_SHA1) return SHA_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA224) return SHA224_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA256) return SHA256_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA384) return SHA384_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA512) return SHA512_DIGEST_LENGTH;  
    else return 64; 
})

_(def s2n_hash_algorithm hmac_to_hash(s2n_hmac_algorithm alg)
{
    if (alg == S2N_HMAC_NONE) return S2N_HASH_NONE; 
    if (alg == S2N_HMAC_MD5) return S2N_HASH_MD5; 
    if (alg == S2N_HMAC_SHA1) return S2N_HASH_SHA1; 
    if (alg == S2N_HMAC_SHA224) return S2N_HASH_SHA224; 
    if (alg == S2N_HMAC_SHA256) return S2N_HASH_SHA256; 
    if (alg == S2N_HMAC_SHA384) return S2N_HASH_SHA384; 
    if (alg == S2N_HMAC_SHA512) return S2N_HASH_SHA512; 
    if (alg == S2N_HMAC_SSLv3_MD5) return S2N_HASH_MD5; 
    if (alg == S2N_HMAC_SSLv3_SHA1) return S2N_HASH_SHA1; 
    else return S2N_HASH_NONE; 
})

_(def \bool is_sslv3(s2n_hmac_algorithm alg)
{
    return (alg>=7 && alg<=8); 
})

_(def \bool is_valid_hmac(s2n_hmac_algorithm alg)
{
    return (alg>=0 && alg<=8); 
})

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires is_valid_hmac(alg))
    _(writes \extent(state))
    _(ensures state->message == repeat(0x0, 0))
    _(ensures \result == 0)
    _(ensures WRAPPED_VALID(state))
    _(ensures state->alg == alg)
    _(ensures state->key == make_num((uint8_t *)key, klen))
    _(decreases 0)
;
  
extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(maintains WRAPPED_VALID(state))
    _(requires \thread_local_array((uint8_t *)in, size))
    _(requires !(\domain_root(\embedding((uint8_t *)in)) \in \domain(state)))
    _(writes state)
    _(ensures state->message == concatenate(\old(state->message), make_num((uint8_t *)in, size)))
    _(ensures UNCHANGED_HMAC_ALG_KEY)
    _(ensures \result == 0)
;

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state,  \array_range(_(uint8_t *)outt, size)) 
    _(ensures is_sslv3(state->alg) ==> make_num((uint8_t *)outt, size) == 
        hashVal(concatenate(concatenate(state->key, OPAD),
        hashVal(concatenate(concatenate(state->key, IPAD), state->message),
        hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))
    _(ensures state->alg && state->key.len>L && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt, size) == hashVal(concatenate(xor(Kprime2, OPAD),
        hashVal(concatenate(xor(Kprime2, IPAD), state->message), hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))  
    _(ensures state->alg && state->key.len<=L && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt, size) == hashVal(concatenate(xor(Kprime, OPAD), hashVal(concatenate(xor(Kprime,
        IPAD), state->message), hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))  
    _(ensures !state->alg ==> make_num((uint8_t *)outt, size) == repeat(0x0, 0))
    _(ensures UNCHANGED_HMAC_ALG_KEY)
    _(ensures \unchanged(state->message))
    _(ensures !state->valid)
    _(ensures \result == 0)
;

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires !is_sslv3(state->alg))
    _(writes state, \array_range(_(uint8_t *)outt, size))
    _(ensures is_sslv3(state->alg) ==> make_num((uint8_t *)outt, size) == 
        hashVal(concatenate(concatenate(state->key, OPAD),
        hashVal(concatenate(concatenate(state->key, IPAD), \old(state->message)),
        hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))
    _(ensures state->alg && state->key.len>L && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt, size) == hashVal(concatenate(xor(Kprime2, OPAD),
        hashVal(concatenate(xor(Kprime2,
        IPAD), \old(state->message)), hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))  
    _(ensures state->alg && state->key.len<=L && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt, size) == hashVal(concatenate(xor(Kprime,
        OPAD), hashVal(concatenate(xor(Kprime,
        IPAD), \old(state->message)), hmac_to_hash(state->alg))), hmac_to_hash(state->alg)))  
    _(ensures !state->alg ==> make_num((uint8_t *)outt, size) == repeat(0x0, 0))
    _(ensures \result == 0)   
;

extern int s2n_hmac_reset(struct s2n_hmac_state *state)
    _(maintains \wrapped(state))
    _(requires is_valid_hmac(state->alg))
    _(writes state)
    _(ensures state->message == repeat(0x0, 0))
    _(ensures UNCHANGED_HMAC_ALG_KEY)
    _(ensures \result == 0)
    _(ensures state->valid)
    _(decreases 0) 
;

#define mega_ensures(in1, in2) \
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_ ## in1    ==> \union_active(&(&s->inner)->hash_ctx. ## in2)    && \
        \union_active(&(&s->outer)->hash_ctx. ## in2)    && \union_active(&(&s->inner_just_key)->hash_ctx. ## in2)    \
        && \unchanged((&(&s->inner_just_key)->hash_ctx. ## in2)->val)    && \unchanged((&(&s->inner)->hash_ctx. ## in2)->val)    \
        && \unchanged((&(&s->outer)->hash_ctx. ## in2)->val)    && \unchanged((&(&s->inner_just_key)->hash_ctx. ## in2)->valid)\
        && \unchanged((&(&s->inner)->hash_ctx. ## in2)->valid)    && \unchanged((&(&s->outer)->hash_ctx. ## in2)->valid))
  

_(ghost int hmac_state_destroy(struct s2n_hmac_state *s)
    _(requires \wrapped(s) || \mutable(s))
    _(writes s)
    _(ensures \unchanged(make_num(s->xor_pad, s->block_size)))
    _(ensures \extent_fresh(s))
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
    _(ensures \unchanged((&s->inner)->alg))
    _(ensures \unchanged((&s->inner_just_key)->alg))
    _(ensures \unchanged((&s->outer)->alg))
    _(ensures \unchanged(s->block_size))
    _(ensures \unchanged(s->digest_size))
    _(ensures \unchanged(s->hash_block_size))
    _(ensures \unchanged(s->currently_in_hash_block))
    _(ensures \unchanged((&s->inner)->hashState))
    _(ensures \unchanged((&s->outer)->hashState))
    _(ensures \unchanged(s->message))
    _(ensures \unchanged((&s->inner_just_key)->hashState))
    _(ensures \unchanged(s->valid) && \unchanged((&s->inner)->valid) && \unchanged((&s->outer)->valid) && 
        \unchanged((&s->inner_just_key)->valid))
    mega_ensures(MD5,md5)
    mega_ensures(SHA1,md5)
    mega_ensures(SHA224,md5)
    mega_ensures(SHA256,md5)
    mega_ensures(SHA384,md5)
    mega_ensures(SHA512,sha512)
    _(ensures \unchanged(s->key))
    _(ensures \unchanged(hashVal(s->key, hmac_to_hash(s->alg))))
    _(decreases 0)
;)

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(maintains WRAPPED_VALID(from))
    _(requires from != to)
    _(writes \extent(to), from)
    _(ensures WRAPPED_VALID(to))
    _(ensures \result == 0)
    _(ensures to->message == from->message)
    _(ensures \unchanged(from->message))
; 



