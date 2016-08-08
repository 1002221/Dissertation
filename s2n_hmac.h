
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

#include <stdint.h>
#include <vcc.h>
#include "s2n_hash.h"
#include <stdio.h>
#include <stdlib.h>

#define SYSTEM_PAGE_SIZE() 394857

#define GUARD( x )      if ( (x) < 0 ) return -1
#define GUARD_PTR( x )  if ( (x) < 0 ) return NULL

#define notnull_check( ptr )    do { if ( (ptr) == NULL ) { return -1; } }                          while(0)
#define memcpy_check( d, s, n ) do { if ( (n) ) { notnull_check( (d) ); memcpy( (d), (s), (n)); } } while(0)
#define memset_check( d, c, n ) do { if ( (n) ) { notnull_check( (d) ); memset( (d), (c), (n)); } } while(0)

#define gte_check(n, min)  do { if ( (n) < min ) { return -1; /*S2N_ERROR(S2N_ERR_SAFETY);*/ } } while(0)
#define lte_check(n, max)  do { if ( (n) > max ) { S2N_ERROR(S2N_ERR_SAFETY); } } while(0)
#define gt_check(n, min)  do { if ( (n) <= min ) { S2N_ERROR(S2N_ERR_SAFETY); } } while(0)
#define lt_check(n, max)  do { if ( (n) >= max ) { S2N_ERROR(S2N_ERR_SAFETY); } } while(0)
#define eq_check(a, b)  do { if ( (a) != (b) ) { return -1;/*S2N_ERROR(S2N_ERR_SAFETY);*/ } } while(0)
#define ne_check(a, b)  do { if ( (a) == (b) ) { S2N_ERROR(S2N_ERR_SAFETY); } } while(0)
#define inclusive_range_check( low, n, high )  gte_check(n, low); lte_check(n, high)
#define exclusive_range_check( low, n, high )  gt_check(n, low); lt_check(n, high)

uint8_t *  memset(uint8_t * dst, uint8_t val, size_t size)
       _(requires \mutable_array(dst,size))
       _(writes \array_range(dst,size))
       _(ensures \forall size_t i; i < size ==> dst[i] == val)
       _(ensures \result == dst)
;
 
uint8_t * memcpy(uint8_t *dst, uint8_t *src, size_t size)
       _(writes \array_range(dst,size))
       _(requires \thread_local_array(src,size))
       _(requires \arrays_disjoint(dst,size, src,size))
       _(ensures \forall size_t i; i < size ==> dst[i] == \old(src[i]))
       _(ensures \result == dst)
       _(decreases 0)
;

/*#define wrap_state(s) \
    if(s->alg == S2N_HASH_NONE) { \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx})} \
    else if(s->alg == S2N_HASH_MD5) { \
        _(union_reinterpret &s->hash_ctx.md5) \ 
        _(wrap &s->hash_ctx.md5) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.md5, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_SHA1) { \
        _(union_reinterpret &s->hash_ctx.sha1) \ 
        _(wrap &s->hash_ctx.sha1) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.sha1, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_SHA224) { \
        _(union_reinterpret &s->hash_ctx.sha224) \ 
        _(wrap &s->hash_ctx.sha224) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.sha224, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_SHA256) { \
        _(union_reinterpret &s->hash_ctx.sha256) \ 
        _(wrap &s->hash_ctx.sha256) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.sha256, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_SHA384) { \
        _(union_reinterpret &s->hash_ctx.sha384) \ 
        _(wrap &s->hash_ctx.sha384) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.sha384, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_SHA512) { \
        _(union_reinterpret &s->hash_ctx.sha512)  \
        _(wrap &s->hash_ctx.sha512) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.sha512, &s->hash_ctx})} \
    else if(s->alg == S2N_HASH_MD5_SHA1) { \
        _(union_reinterpret &s->hash_ctx.md5_sha1) \ 
        _(wrap &s->hash_ctx.md5_sha1.sha1) \
        _(wrap &s->hash_ctx.md5_sha1.md5) \
        _(wrap &s->hash_ctx.md5_sha1) \
        _(wrap &s->hash_ctx) \
        _(ghost s->\owns = {&s->hash_ctx.md5_sha1, &s->hash_ctx.md5_sha1.sha1, &s->hash_ctx.md5_sha1.md5, &s->hash_ctx})} \
    else {_(assert 0)} */

typedef enum { S2N_HMAC_NONE, S2N_HMAC_MD5, S2N_HMAC_SHA1, S2N_HMAC_SHA224, S2N_HMAC_SHA256, S2N_HMAC_SHA384,
    S2N_HMAC_SHA512, S2N_HMAC_SSLv3_MD5, S2N_HMAC_SSLv3_SHA1
} s2n_hmac_algorithm;

struct s2n_hmac_state {
    s2n_hmac_algorithm alg;

    uint16_t hash_block_size;
    uint32_t currently_in_hash_block;
    uint16_t block_size;
    uint8_t digest_size;

    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;

    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];
    _(ghost Num xorpad)
    _(invariant valid(xorpad))
    _(invariant xorpad.len == block_size)
    _(invariant xorpad.val == (\lambda \natural i; i<128? xor_pad[i] : (uint8_t)0))
    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
    _(ghost Num digestpad)
    _(invariant valid(digestpad))
    _(invariant digestpad.len == digest_size)
    _(invariant digestpad.val == (\lambda \natural i; i<SHA512_DIGEST_LENGTH? digest_pad[i] : (uint8_t)0))

    _(invariant alg>= 0 && alg <= 8)
    _(invariant (&inner)->alg == hmac_to_hash(alg))
    _(invariant (&inner_just_key)->alg == hmac_to_hash(alg))
    _(invariant (&outer)->alg == hmac_to_hash(alg))
    _(invariant \mine(&inner) && \mine(&outer) && \mine(&inner_just_key))
    _(invariant digest_size == alg_digest_size(hmac_to_hash(alg)))
    _(invariant hash_block_size >= 9)
    _(invariant block_size != 0)
    _(invariant sizeof(xor_pad) >= block_size)
};

typedef union s2n_hmac_state2{
    struct s2n_hmac_state t;
    _(backing_member) uint8_t asBytes[sizeof(struct s2n_hmac_state)];
} s2n_hmac_state2;

extern int s2n_hmac_digest_size(s2n_hmac_algorithm alg)
    _(requires alg >= 0 && alg <= 8)
;

int s2n_hmac_digest_size(s2n_hmac_algorithm alg)
{
    if (alg == S2N_HMAC_SSLv3_MD5) {
        alg = S2N_HMAC_MD5;
    }
    if (alg == S2N_HMAC_SSLv3_SHA1) {
        alg = S2N_HMAC_SHA1;
    }

    return s2n_hash_digest_size((s2n_hash_algorithm) alg);
}

_(def uint16_t block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE) return 64; 
    if (alg == S2N_HMAC_MD5) return 48; 
    if (alg == S2N_HMAC_SHA1) return 40; 
    if (alg == S2N_HMAC_SHA224) return 64; 
    if (alg == S2N_HMAC_SHA256) return 64; 
    if (alg == S2N_HMAC_SHA384) return 128; 
    if (alg == S2N_HMAC_SHA512) return 128; 
    if (alg == S2N_HMAC_SSLv3_MD5) return 48; 
    if (alg == S2N_HMAC_SSLv3_SHA1) return 40; 
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
    else return S2N_HASH_NONE ; 
})

/*static int s2n_sslv3_mac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \extent_mutable(state))
    _(requires state->alg == S2N_HMAC_SSLv3_SHA1 || state->alg == S2N_HMAC_SSLv3_MD5)
    _(requires state->alg == S2N_HMAC_SSLv3_SHA1 ==> state->block_size == 40 && state->digest_size == SHA_DIGEST_LENGTH)
    _(requires state->alg == S2N_HMAC_SSLv3_MD5 ==> state->block_size == 48 && state->digest_size == MD5_DIGEST_LENGTH)
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires sizeof(state->xor_pad) >= state->block_size)
    _(requires sizeof(state->digest_pad) >= state->digest_size)
    _(requires sizeof(state->xor_pad) >= state->block_size)
    _(requires sizeof(state->digest_pad) >= state->digest_size)
    _(requires state->alg == alg)
    _(requires state->currently_in_hash_block == 0)
    _(requires state->hash_block_size == 64)
    _(maintains state->block_size == block_size_alg(alg))
    _(writes \extent(state))
    //_(ensures !\result ==> \wrapped(state))
    _(ensures \result <= 0)
    _(decreases 0)
{
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;

    if (alg == S2N_HMAC_SSLv3_MD5) {
        hash_alg = S2N_HASH_MD5;
        _(assert 0)
    }
    if (alg == S2N_HMAC_SSLv3_SHA1) {
        hash_alg = S2N_HASH_SHA1;
        _(assert 0)
    }

    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size)){
        state->xor_pad[i] = 0x36;
    }

    GUARD(s2n_hash_init(&state->inner_just_key, hash_alg));
    GUARD(s2n_hash_update(&state->inner_just_key, key, klen));
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));

    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size)){
        state->xor_pad[i] = 0x5c;
    }

    GUARD(s2n_hash_init(&state->outer, hash_alg));
    GUARD(s2n_hash_update(&state->outer, key, klen));
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));

    /* Copy inner_just_key to inner */
    /*return 0;
    //return s2n_hmac_reset(state);
}*/

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \extent_mutable(state))
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)state->digest_pad, state->digest_size))
    _(requires \thread_local_array((uint8_t *)state->xor_pad, state->digest_size))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires alg >= 0 && alg <= 8)
    _(writes \extent(state))
    _(ensures \result <= 0)
    //_(ensures !\result ==> \wrapped(state))
    _(ensures state->block_size == block_size_alg(alg))
    //no - we want a postcondition relating xorpad to klen. this is gonna be really complicated.
    _(ensures !\result && klen <= block_size_alg(alg) && alg<=6 ==> state->xorpad.val == (\lambda \natural i; i<klen? (uint8_t)(((uint8_t *)(key))[i]^(uint8_t)(0x5c)) : (i<block_size_alg(alg)? (uint8_t)(0x5c) :(uint8_t)0)))
    _(ensures !\result && klen > block_size_alg(alg) && alg==2 ==> state->xorpad.val == (\lambda \natural i; i<state->digest_size? (uint8_t)((hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val)[i]^(uint8_t)(0x5c)) : (i<block_size_alg(alg)? (uint8_t)(0x5c) :(uint8_t)0)))
    _(ensures !\result && alg<=6 ==> hashState(&state->inner,0) == concatenate(\old(hashState(&state->inner,0)),state->xorpad))
    _(ensures !\result && alg<=6  ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(decreases 0)
;

int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
{
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;
    state->currently_in_hash_block = 0;
    state->digest_size = 0;
    state->block_size = 64;
    state->hash_block_size = 64; 
    switch (alg) {
    case S2N_HMAC_NONE:
        break;
    case S2N_HMAC_SSLv3_MD5:
        state->block_size = 48;
        hash_alg = S2N_HASH_MD5; //USER-ADDED
        state->digest_size = MD5_DIGEST_LENGTH;//USER-ADDED
         //Fall through ... 
        break; //USER-ADDED
    case S2N_HMAC_MD5:
        state->block_size = 48; //USER-ADDED
        hash_alg = S2N_HASH_MD5;
        state->digest_size = MD5_DIGEST_LENGTH;
        break;
    case S2N_HMAC_SSLv3_SHA1:
        state->block_size = 40;
        state->digest_size = SHA_DIGEST_LENGTH; //USER-ADDED
        hash_alg = S2N_HASH_SHA1; //USER-ADDED
        // Fall through ... */
        break; //USER-ADDED
    case S2N_HMAC_SHA1:
        hash_alg = S2N_HASH_SHA1;
        state->block_size = 40; //USER-ADDED
        state->digest_size = SHA_DIGEST_LENGTH;
        break;
    case S2N_HMAC_SHA224:
        hash_alg = S2N_HASH_SHA224;
        state->digest_size = SHA224_DIGEST_LENGTH;
        break;
    case S2N_HMAC_SHA256:
        hash_alg = S2N_HASH_SHA256;
        state->digest_size = SHA256_DIGEST_LENGTH;
        break;
    case S2N_HMAC_SHA384:
        hash_alg = S2N_HASH_SHA384;
        state->digest_size = SHA384_DIGEST_LENGTH;
        state->block_size = 128;
        state->hash_block_size = 128;
        break;
    case S2N_HMAC_SHA512:
        hash_alg = S2N_HASH_SHA512;
        state->digest_size = SHA512_DIGEST_LENGTH;
        state->block_size = 128;
        state->hash_block_size = 128;
        break;
    default:
        //S2N_ERROR(S2N_ERR_HMAC_INVALID_ALGORITHM);
        _(assert 0)
    }
    _(assert sizeof(state->xor_pad) >= state->block_size)
    _(assert sizeof(state->digest_pad) >= state->digest_size)
    //gte_check(sizeof(state->xor_pad), state->block_size);
    //gte_check(sizeof(state->digest_pad), state->digest_size);
    _(assert sizeof(state->xor_pad) >= state->block_size)
    _(assert sizeof(state->digest_pad) >= state->digest_size)
    
    state->alg = alg;
    
    /*if (alg == S2N_HMAC_SSLv3_SHA1 || alg == S2N_HMAC_SSLv3_MD5) {
        return s2n_sslv3_mac_init(state, alg, key, klen);
    }*/
    GUARD(s2n_hash_init(&state->inner_just_key, hash_alg));
    GUARD(s2n_hash_init(&state->outer, hash_alg));
    _(assert hash_alg == S2N_HASH_SHA1 ==> (&(&state->outer)->hash_ctx.sha1)->val == repeat((uint8_t)0,0))
    uint32_t copied = klen;
    _(ghost state->xorpad.len = state->block_size) //technically, no, but this is the only part we use
    if (klen > state->block_size) {
        _(ghost \state t = \now())
        GUARD(s2n_hash_update(&state->outer, key, klen));
        _(assert hash_alg == S2N_HASH_SHA1 ==> (&(&state->outer)->hash_ctx.sha1)->val == concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)))
        GUARD(s2n_hash_digest(&state->outer, state->digest_pad, state->digest_size)); 
        _(assert \forall size_t i; i<state->digest_size && hmac_to_hash(state->alg) == S2N_HASH_SHA1 ==> state->digest_pad[i] == hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val[i])
        //_(assert \forall size_t i; i>=state->digest_size && hmac_to_hash(state->alg) == S2N_HASH_SHA1 ==> state->digest_pad[i] == (uint8_t)0)
        _(ghost state->digestpad.len = state->digest_size)
        _(ghost state->digestpad.val = (\lambda \natural i; i<state->digestpad.len? state->digest_pad[i] : (uint8_t)0))
        _(assert state->digestpad.len == state->digest_size)
        _(assert state->digest_size ==> state->xor_pad != NULL)
        memcpy/*_check*/(state->xor_pad, state->digest_pad, state->digest_size);
        _(ghost state->xorpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
        _(assert \forall size_t i; i<state->digest_size && state->alg==2 ==> state->xor_pad[i] == hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val[i])
        copied = state->digest_size;
    } else {
        _(assert klen ==> state->xor_pad != NULL)
        memcpy/*_check*/(state->xor_pad, key, klen);
        _(ghost state->xorpad.val = (\lambda \natural i; i<klen? ((uint8_t *)(key))[i] : (uint8_t)0))
    }
    _(ghost \state s = \now())
    _(assert klen <= state->block_size ==> state->xorpad.val==(\lambda \natural i; i<klen? ((uint8_t *)(key))[i] : (uint8_t)0))
    _(assert klen > state->block_size && state->alg == 2 ==> state->xorpad.val==(\lambda \natural i; i<state->digest_size? hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val[i] : (uint8_t)0))
    _(assert klen > state->block_size && state->alg == 2 ==> \at(s,state->xorpad.val)==(\lambda \natural i; i<(\natural)state->digest_size? (hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,(size_t)klen)),S2N_HASH_SHA1)).val[i] : (uint8_t)0))
    for (int i = 0; i < (int) copied; i++) 
        _(writes \array_range(state->xor_pad,copied), &state->xorpad)
        _(decreases (int)copied - i)
        _(invariant \unchanged(state->digest_size))
        _(invariant \unchanged(state->block_size))
        _(invariant \unchanged(state->alg))
        _(invariant i>= 0 && i<= (int)copied)
        _(invariant klen > state->block_size ==> copied == state->digest_size)
        _(invariant state->xorpad == xor(\at(s,state->xorpad),concatenate(repeat(0x36,(\natural)i),repeat((uint8_t)0,state->xorpad.len-(\natural)(i)))))
    {
        state->xor_pad[i] ^= (uint8_t)0x36;
        _(ghost state->xorpad.val[(\natural)i] = \at(s,state->xorpad.val[(\natural)i]) ^ (uint8_t)0x36)
    }
    _(assert 0 <= copied)
    _(assert state->xorpad == xor(\at(s,state->xorpad),concatenate(repeat((uint8_t)0x36,(\natural)copied),repeat((uint8_t)0,(\natural)(state->block_size-copied)))))
    _(assert klen > state->block_size ==> copied == state->digest_size)
    _(assert klen > state->block_size && state->alg == 2 ==> state->xorpad.val==(\lambda \natural i; i<state->digest_size? (uint8_t)(\at(s,state->xorpad).val[i]^(uint8_t)0x36) : (uint8_t)0))
    _(assert klen > state->block_size && state->alg == 2 ==> \at(s,state->xorpad).val==(\lambda \natural i; i<(\natural)state->digest_size? (hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,(size_t)klen)),S2N_HASH_SHA1)).val[i] : (uint8_t)0))
    _(assert klen > state->block_size && state->alg == 2 ==> state->xorpad.val==(\lambda \natural i; i<state->digest_size? (uint8_t)(hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val[i]^(uint8_t)0x36) : (uint8_t)0))
    _(ghost \state s1 = \now())
    for (int i = (int) copied; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad + copied,state->block_size - copied))
        _(writes &state->xorpad)
        _(decreases state->block_size - i)
        _(invariant valid(state->xorpad))
        _(invariant state->xorpad == num_segment(\at(s1,state->xorpad), (\natural)copied, (\natural)i, (uint8_t)0x36))
        _(invariant i>=(int)copied && i<= state->block_size){
        state->xor_pad[i] = 0x36;
        _(ghost state->xorpad.val[(\natural)i] = (uint8_t)0x36)
    }
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));
    _(ghost \state s2 = \now())
    //_(assert state->xorpad == xor(\at(s,state->xorpad),repeat((uint8_t)0x36,state->xorpad.len)))
    // 0x36 xor 0x5c == 0x6a 
    _(assert klen > state->block_size && state->alg == 2 ==> state->xorpad.val==(\lambda \natural i; i<copied? (uint8_t)(hashVal(concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)),S2N_HASH_SHA1).val[i]^(uint8_t)0x36) : (i<state->digest_size? (uint8_t)0x36 : (uint8_t)0)))
    for (int i = 0; i < state->block_size; i++) 
    _(writes \array_range(state->xor_pad,state->block_size))
    _(invariant i>=0 && i <= state->block_size)
    _(decreases state->block_size - i)
    _(invariant state->xorpad == xor(\at(s2,state->xorpad),concatenate(repeat(0x6a,(\natural)i),repeat((uint8_t)0,state->xorpad.len-(\natural)i))))
        _(writes &state->xorpad){
        state->xor_pad[i] ^= 0x6a;
        _(ghost state->xorpad.val[(\natural)i] = \at(s2,state->xorpad.val[(\natural)i])^(uint8_t)0x6a)
    }
    _(assert state->xorpad == xor(\at(s2,state->xorpad),repeat((uint8_t)(0x36 ^ 0x5c),state->xorpad.len)))
    _(assert \at(s2,state->xorpad) == xor(\at(s,state->xorpad),repeat((uint8_t)0x36,state->xorpad.len)))
    _(assert state->xorpad == xor(xor(\at(s,state->xorpad),repeat((uint8_t)0x36,\at(s,state->xorpad).len)),repeat((uint8_t)(0x36 ^ 0x5c),\at(s,state->xorpad).len)))
    _(ghost xor_combine((uint8_t)0x36,(uint8_t)(0x36 ^ 0x5c),\at(s,state->xorpad)))
    _(assert state->xorpad == xor(\at(s,state->xorpad),repeat((uint8_t)(0x36 ^ (0x36 ^ 0x5c)),\at(s,state->xorpad).len)))
    _(assert state->xorpad == xor(\at(s,state->xorpad),repeat((uint8_t)0x5c,state->xorpad.len)))
    _(assert hmac_to_hash(state->alg) == S2N_HASH_MD5 ==> valid((&(&state->inner_just_key)->hash_ctx.md5)->val))
    return 0;
    //return s2n_hmac_reset(state);
}

extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(requires \wrapped(state))
    _(requires \thread_local_array((uint8_t *)in,size))
    _(requires state->currently_in_hash_block + (4294949760 + size) % state->hash_block_size <= _UI32_MAX - SYSTEM_PAGE_SIZE())
    _(writes state)
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result && state->alg>0 && state->alg<=6 ==> hashState(&state->inner,0) == concatenate(\old(hashState(&state->inner,0)),make_num((uint8_t *)in,size)))
    _(ensures \result <= 0);

int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
{
    /* Keep track of how much of the current hash block is full
     *
     * Why the 4294949760 constant in this code? 4294949760 is the highest 32-bit
     * value that is congruent to 0 modulo all of our HMAC block sizes, that is also
     * at least 16k smaller than 2^32. It therefore has no effect on the mathematical
     * result, and no valid record size can cause it to overflow.
     * 
     * The value was found with the following python code;
     * 
     * x = (2 ** 32) - (2 ** 14)
     * while True:
     *   if x % 40 | x % 48 | x % 64 | x % 128 == 0:
     *     break
     *   x -= 1
     * print x
     *
     * What it does do however is ensure that the mod operation takes a
     * constant number of instruction cycles, regardless of the size of the
     * input. On some platforms, including Intel, the operation can take a
     * smaller number of cycles if the input is "small".
     */
    _(unwrap state)
    state->currently_in_hash_block += _(unchecked) (4294949760 + size) % state->hash_block_size;
    state->currently_in_hash_block %= state->block_size;
    { 
        int res = s2n_hash_update(&state->inner, in, size);
        _(wrap state) 
        return res; 
    }
}


static int s2n_sslv3_mac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires state->alg >= 7 && state->alg <= 8)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures !\result ==> \wrapped(state))
    _(ensures \unchanged(state->hash_block_size))
    _(ensures \result <= 0)
{
    _(unwrap state)
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size)){
        state->xor_pad[i] = 0x5c;
    }
   
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    //memcpy/*_check*//*(&state->inner, &state->outer, sizeof(state->inner));
    state->inner = state->outer; //USER ADDED INSTEAD OF MEMCPY
    _(unwrap &state->inner)
    (&state->inner)->alg = (&state->outer)->alg;
    _(wrap &state->inner)
    GUARD(s2n_hash_update(&state->inner, state->digest_pad, state->digest_size));

    {
        int res= s2n_hash_digest(&state->inner, outt, size);
        _(wrap state)
        return res;
    }
}

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires state->alg <= 6)
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures !\result ==> \wrapped(state))
    _(ensures \unchanged(state->hash_block_size))
    _(ensures !\result && state->alg && state->alg<=6 ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures !\result && state->alg && state->alg<=6 ==> make_num((uint8_t *)outt,size)==hashVal(concatenate(concatenate(repeat((uint8_t)0,0),state->xorpad),state->digestpad),hmac_to_hash(state->alg)))  
    _(ensures !\result && state->alg && state->alg<=6 ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(ensures \result <= 0)
;

int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    if (state->alg == S2N_HMAC_SSLv3_SHA1 || state->alg == S2N_HMAC_SSLv3_MD5) {
        return s2n_sslv3_mac_digest(state, outt, size);
    }
    _(unwrap state) 
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
    _(assert state->alg == S2N_HASH_MD5 ==> state->digestpad == hashVal(\old((&(&state->inner)->hash_ctx.md5)->val),S2N_HASH_MD5))
    GUARD(s2n_hash_reset(&state->outer));
    _(assert state->alg == S2N_HASH_MD5 ==> (&(&state->outer)->hash_ctx.md5)->val == repeat((uint8_t)0,0))
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));
    _(assert state->alg == S2N_HASH_MD5 ==> (&(&state->outer)->hash_ctx.md5)->val == concatenate(repeat((uint8_t)0,0),state->xorpad))
    GUARD(s2n_hash_update(&state->outer, state->digest_pad, state->digest_size));
    _(assert state->alg == S2N_HASH_MD5 ==> (&(&state->outer)->hash_ctx.md5)->val == concatenate(concatenate(repeat((uint8_t)0,0),state->xorpad),state->digestpad))
    { 
        int res = s2n_hash_digest(&state->outer,outt, size);
        _(assert state->alg == S2N_HASH_MD5 ==> make_num((uint8_t *)outt,size)==hashVal(concatenate(concatenate(repeat((uint8_t)0,0),state->xorpad),state->digestpad),S2N_HASH_MD5))
        _(wrap state)
        return res; 
    }
}

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(outt,size))
    _(ensures !\result ==> \wrapped(state))
    _(ensures \result <= 0)    
    ;

int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    GUARD(s2n_hmac_digest(state, outt, size));

    /* If there were 9 or more bytes of space left in the current hash block
     * then the serialized length, plus an 0x80 byte, will have fit in that block. 
     * If there were fewer than 9 then adding the length will have caused an extra 
     * compression block round. This digest function always does two compression rounds,
     * even if there is no need for the second.
     */
    if (state->currently_in_hash_block > (state->hash_block_size - 9))
    {
        return 0;
    }

    _(unwrap state)
    
    { 
        int res = s2n_hash_update(&state->inner, state->xor_pad, state->hash_block_size);
        _(wrap state) 
        return res; 
    }
}

extern int s2n_constant_time_equals(const uint8_t *a, const uint8_t *b, uint32_t len)
    _(requires \thread_local_array((uint8_t *)a,len))
    _(requires \thread_local_array((uint8_t *)b,len))
    _(ensures (\forall uint8_t i; i<len ==> ((uint8_t *)(a))[i]==((uint8_t *)(b))[i]) ==> \result == 1)
    _(ensures (\exists uint8_t i; i<len && ((uint8_t *)(a))[i] != ((uint8_t *)(b))[i]) ==> \result == 0)
;

extern int s2n_hmac_digest_verify(const void *a, const void *b, uint32_t len)
    _(requires \thread_local_array((uint8_t *)a,len))
    _(requires \thread_local_array((uint8_t *)b,len))
    _(ensures (\forall uint8_t i; i<len ==> ((uint8_t *)(a))[i]== ((uint8_t *)(b))[i]) ==> \result == 0)
    _(ensures (\exists uint8_t i; i<len && ((uint8_t *)(a))[i] != ((uint8_t *)(b))[i]) ==> \result == -1)
;

int s2n_hmac_digest_verify(const void *a, const void *b, uint32_t len)
{
    return 0 - !s2n_constant_time_equals((uint8_t *)a, (uint8_t *)b, len);
}



extern int s2n_hmac_reset(struct s2n_hmac_state *state)
    _(requires \mutable(state) && \extent_mutable(&state->inner) && \wrapped(&state->inner_just_key) && \wrapped(&state->outer))
    _(requires (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    _(requires (&state->outer)->alg == hmac_to_hash(state->alg))
    _(requires state->alg>=0 && state->alg<=6)
    _(requires state->hash_block_size >= 9)
    _(requires state->digest_size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires state->block_size != 0)
    _(requires sizeof(state->xor_pad) >= state->block_size)
    _(requires state->xorpad.val == (\lambda \natural i; i<128? state->xor_pad[i]:(uint8_t)0))
    _(requires state->xorpad.len == sizeof(state->xor_pad))
    _(requires valid(state->xorpad))
    _(writes \span(state), \extent(&state->inner), &state->inner_just_key, &state->outer)
    _(requires hmac_to_hash(state->alg) == S2N_HASH_MD5 ==> valid((&(&state->inner_just_key)->hash_ctx.md5)->val))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA1 ==> valid((&(&state->inner_just_key)->hash_ctx.sha1)->val))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA224 ==> valid((&(&state->inner_just_key)->hash_ctx.sha224)->val))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA256 ==> valid((&(&state->inner_just_key)->hash_ctx.sha256)->val))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA384 ==> valid((&(&state->inner_just_key)->hash_ctx.sha384)->val))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA512 ==> valid((&(&state->inner_just_key)->hash_ctx.sha512)->val))
    _(requires valid(state->digestpad))
    _(requires state->digestpad.val == (\lambda \natural i; i<64? state->digest_pad[i]:(uint8_t)0))
    _(requires state->digestpad.len == sizeof(state->digest_pad))
    _(ensures !\result && state->alg == S2N_HMAC_MD5 ==> (&(&state->inner)->hash_ctx.md5)->val == (&(&state->inner)->hash_ctx.md5)->val)
    _(ensures !\result && state->alg == S2N_HMAC_SHA1 ==> (&(&state->inner)->hash_ctx.sha1)->val == (&(&state->inner)->hash_ctx.sha1)->val)
    _(ensures !\result && state->alg == S2N_HMAC_SHA224 ==> (&(&state->inner)->hash_ctx.sha224)->val == (&(&state->inner)->hash_ctx.sha224)->val)
    _(ensures !\result && state->alg == S2N_HMAC_SHA256 ==> (&(&state->inner)->hash_ctx.sha256)->val == (&(&state->inner)->hash_ctx.sha256)->val)
    _(ensures !\result && state->alg == S2N_HMAC_SHA384 ==> (&(&state->inner)->hash_ctx.sha384)->val == (&(&state->inner)->hash_ctx.sha384)->val)
    _(ensures !\result && state->alg == S2N_HMAC_SHA512 ==> (&(&state->inner)->hash_ctx.sha512)->val == (&(&state->inner)->hash_ctx.sha512)->val)
    _(ensures (&state->inner)->alg == (&state->inner_just_key)->alg)
    _(ensures \wrapped(state))
    _(ensures \result == 0)
    _(decreases 0)
    _(ensures \unchanged(state->xorpad))   
;

int s2n_hmac_reset(struct s2n_hmac_state *state)
{
    _(assert hmac_to_hash(state->alg) == S2N_HASH_SHA256 ==> valid((&(&state->inner_just_key)->hash_ctx.sha256)->val))
    state->currently_in_hash_block = 0;
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    hash_state_destroy(&state->inner_just_key);
    //memcpy/*_check*//*(&state->inner, &state->inner_just_key, sizeof(state->inner));
    state->inner = state->inner_just_key;
    _(assert (&state->inner)->alg == (&state->inner_just_key)->alg)
    _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    switch((&state->inner_just_key)->alg){
    case S2N_HASH_NONE:
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx})
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx})
    break;
    case S2N_HASH_MD5:   
        _(wrap &(&state->inner_just_key)->hash_ctx.md5)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.md5, &(&state->inner_just_key)->hash_ctx}) 
        _(union_reinterpret &(&state->inner)->hash_ctx.md5)
        _(ghost (&(&state->inner)->hash_ctx.md5)->val = (&(&state->inner_just_key)->hash_ctx.md5)->val)
        _(wrap &(&state->inner)->hash_ctx.md5)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.md5, &(&state->inner)->hash_ctx})
    break;
    case S2N_HASH_SHA1:   
        _(wrap &(&state->inner_just_key)->hash_ctx.sha1)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha1, &(&state->inner_just_key)->hash_ctx}) 
        _(union_reinterpret &(&state->inner)->hash_ctx.sha1)   
        _(ghost (&(&state->inner)->hash_ctx.sha1)->val = (&(&state->inner_just_key)->hash_ctx.sha1)->val)
        _(wrap &(&state->inner)->hash_ctx.sha1)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha1, &(&state->inner)->hash_ctx})
    break;
    case S2N_HASH_SHA224:    
        _(wrap &(&state->inner_just_key)->hash_ctx.sha224)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha224, &(&state->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&state->inner)->hash_ctx.sha224)   
        _(ghost (&(&state->inner)->hash_ctx.sha224)->val = (&(&state->inner_just_key)->hash_ctx.sha224)->val)
        _(wrap &(&state->inner)->hash_ctx.sha224)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha224, &(&state->inner)->hash_ctx})  
    break;
    case S2N_HASH_SHA256:
        _(wrap &(&state->inner_just_key)->hash_ctx.sha256)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha256, &(&state->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&state->inner)->hash_ctx.sha256)
        _(ghost (&(&state->inner)->hash_ctx.sha256)->val = (&(&state->inner_just_key)->hash_ctx.sha256)->val)
        _(wrap &(&state->inner)->hash_ctx.sha256)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha256, &(&state->inner)->hash_ctx}) 
    break;
    case S2N_HASH_SHA384:  
        _(wrap &(&state->inner_just_key)->hash_ctx.sha384)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha384, &(&state->inner_just_key)->hash_ctx})
        _(union_reinterpret &(&state->inner)->hash_ctx.sha384)   
        _(ghost (&(&state->inner)->hash_ctx.sha384)->val = (&(&state->inner_just_key)->hash_ctx.sha384)->val)
        _(wrap &(&state->inner)->hash_ctx.sha384)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha384, &(&state->inner)->hash_ctx}) 
    break;
    case S2N_HASH_SHA512:   
        _(wrap &(&state->inner_just_key)->hash_ctx.sha512)  
        _(wrap &(&state->inner_just_key)->hash_ctx)  
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha512, &(&state->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&state->inner)->hash_ctx.sha512)   
        _(ghost (&(&state->inner)->hash_ctx.sha512)->val = (&(&state->inner_just_key)->hash_ctx.sha512)->val)
        _(wrap &(&state->inner)->hash_ctx.sha512)  
        _(wrap &(&state->inner)->hash_ctx)  
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha512, &(&state->inner)->hash_ctx})
    break;
    default: _(assert 0)}
    _(wrap &state->inner_just_key)
    _(wrap &state->inner)
    _(ghost state->\owns = {&state->inner_just_key, &state->inner, &state->outer})
    _(wrap state)
    return 0;
}

int hmac_state_destroy(struct s2n_hmac_state *s)
    _(requires \wrapped(s))
    _(writes s)
    _(ensures \extent_fresh(s))
    _(ensures \extent_mutable(s))
    _(ensures \unchanged(s->alg))
    _(ensures \unchanged((&s->inner)->alg))
    _(ensures \unchanged((&s->inner_just_key)->alg))
    _(ensures \unchanged((&s->outer)->alg))
    _(ensures \unchanged(s->block_size))
    _(ensures \unchanged(s->digest_size))
    _(ensures \unchanged(s->hash_block_size))
    ;

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(requires \wrapped(from))
    _(requires \extent_mutable(to))
    _(requires from != to)
    _(requires to->hash_block_size >= 9)
    _(requires to->block_size != 0)
    _(writes \extent(to), from)
    _(ensures \wrapped(to))
    _(ensures \result <= 0)
; 

int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
{
    _(assert sizeof(struct s2n_hmac_state) ==> to != NULL)
    //memcpy_check(to, from, sizeof(struct s2n_hmac_state));
    _(assert from->alg >= 0 && from->alg <= 8)
    hmac_state_destroy(from);
    *to = *from; //USED ADDED IN PLACE OF MEMCPY
    _(assert to->alg == from->alg)
    _(assert (&to->inner)->alg == (&from->inner)->alg)
    _(assert to->alg >= 0 && to->alg <= 8)
    switch((&to->inner)->alg){
    case S2N_HASH_NONE:
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx})
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx})
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx})
    break;
    case S2N_HASH_MD5: 
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.md5)   
        _(wrap &(&to->inner_just_key)->hash_ctx.md5)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.md5, &(&to->inner_just_key)->hash_ctx}) 
        _(union_reinterpret &(&to->inner)->hash_ctx.md5)   
        _(wrap &(&to->inner)->hash_ctx.md5)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.md5, &(&to->inner)->hash_ctx})
        _(union_reinterpret &(&to->outer)->hash_ctx.md5)   
        _(wrap &(&to->outer)->hash_ctx.md5)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.md5, &(&to->outer)->hash_ctx}) 
        break;
    case S2N_HASH_SHA1: 
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha1)   
        _(wrap &(&to->inner_just_key)->hash_ctx.sha1)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha1, &(&to->inner_just_key)->hash_ctx}) 
        _(union_reinterpret &(&to->inner)->hash_ctx.sha1)   
        _(wrap &(&to->inner)->hash_ctx.sha1)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha1, &(&to->inner)->hash_ctx})
        _(union_reinterpret &(&to->outer)->hash_ctx.sha1)   
        _(wrap &(&to->outer)->hash_ctx.sha1)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha1, &(&to->outer)->hash_ctx})  
    break;
    case S2N_HASH_SHA224:  
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha224)   
        _(wrap &(&to->inner_just_key)->hash_ctx.sha224)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha224, &(&to->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&to->inner)->hash_ctx.sha224)   
        _(wrap &(&to->inner)->hash_ctx.sha224)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha224, &(&to->inner)->hash_ctx})  
        _(union_reinterpret &(&to->outer)->hash_ctx.sha224)   
        _(wrap &(&to->outer)->hash_ctx.sha224)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha224, &(&to->outer)->hash_ctx})  
    break;
    case S2N_HASH_SHA256:
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha256)   
        _(wrap &(&to->inner_just_key)->hash_ctx.sha256)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha256, &(&to->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&to->inner)->hash_ctx.sha256)   
        _(wrap &(&to->inner)->hash_ctx.sha256)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha256, &(&to->inner)->hash_ctx}) 
        _(union_reinterpret &(&to->outer)->hash_ctx.sha256)   
        _(wrap &(&to->outer)->hash_ctx.sha256)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha256, &(&to->outer)->hash_ctx})     
    break;
    case S2N_HASH_SHA384:
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha384)   
        _(wrap &(&to->inner_just_key)->hash_ctx.sha384)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha384, &(&to->inner_just_key)->hash_ctx})
        _(union_reinterpret &(&to->inner)->hash_ctx.sha384)   
        _(wrap &(&to->inner)->hash_ctx.sha384)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha384, &(&to->inner)->hash_ctx}) 
        _(union_reinterpret &(&to->outer)->hash_ctx.sha384)   
        _(wrap &(&to->outer)->hash_ctx.sha384)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha384, &(&to->outer)->hash_ctx}) 
    break;
    case S2N_HASH_SHA512: 
        _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha512)   
        _(wrap &(&to->inner_just_key)->hash_ctx.sha512)  
        _(wrap &(&to->inner_just_key)->hash_ctx)  
        _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha512, &(&to->inner_just_key)->hash_ctx})  
        _(union_reinterpret &(&to->inner)->hash_ctx.sha512)   
        _(wrap &(&to->inner)->hash_ctx.sha512)  
        _(wrap &(&to->inner)->hash_ctx)  
        _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha512, &(&to->inner)->hash_ctx})
        _(union_reinterpret &(&to->outer)->hash_ctx.sha512)   
        _(wrap &(&to->outer)->hash_ctx.sha512)  
        _(wrap &(&to->outer)->hash_ctx)  
        _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha512, &(&to->outer)->hash_ctx})
    break;
    default: _(assert 0)}
    _(wrap &to->inner_just_key)
    _(wrap &to->inner)
    _(wrap &to->outer)
    _(ghost to->\owns = {&to->inner_just_key, &to->inner, &to->outer})
    _(assert \inv(to))
    _(wrap to)
    _(assert \wrapped(to))
    return 0;
}



