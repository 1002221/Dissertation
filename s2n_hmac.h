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
#include "myblob.h"

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

typedef enum { S2N_HMAC_NONE, S2N_HMAC_MD5, S2N_HMAC_SHA1, S2N_HMAC_SHA224, S2N_HMAC_SHA256, S2N_HMAC_SHA384,
    S2N_HMAC_SHA512, S2N_HMAC_SSLv3_MD5, S2N_HMAC_SSLv3_SHA1
} s2n_hmac_algorithm;

struct s2n_hmac_state {
    s2n_hmac_algorithm alg;

    uint16_t hash_block_size;
    uint32_t currently_in_hash_block;
    uint16_t block_size;
    uint8_t digest_size;

    _(ghost Num key)

    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;

    _(invariant key.len <= block_size &&    !is_sslv3(alg)  ==> hashState(&inner_just_key,0) == xor(num_resize(key,block_size),repeat(0x36,block_size)))
    _(invariant key.len > block_size &&     !is_sslv3(alg)  ==> hashState(&inner_just_key,0) == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x36,block_size)))
    _(invariant                             !is_sslv3(alg)  ==> hashState(&outer,0) == repeat((uint8_t)0,0))
    _(invariant                             is_sslv3(alg)   ==> hashState(&inner_just_key,0) == concatenate(key,repeat(0x36,block_size)))
    _(invariant                             is_sslv3(alg) ==> hashState(&outer,0) == concatenate(key,repeat(0x5c,block_size)))
    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];
    _(ghost Num xorpad)
    _(invariant valid(xorpad))
    _(invariant xorpad.len == block_size)
    _(invariant xorpad.val == (\lambda \natural i; i<block_size? xor_pad[i] : (uint8_t)0))
    _(invariant key.len>block_size && !is_sslv3(alg) ==> xorpad == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x5c,block_size)))
    _(invariant key.len<=block_size && !is_sslv3(alg) ==> xorpad == xor(num_resize(key,block_size),repeat(0x5c,block_size)))
    _(invariant is_sslv3(alg) ==> xorpad == repeat((uint8_t)0x5c,block_size))
    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
    _(ghost Num digestpad)
    _(invariant valid(digestpad))
    _(invariant digestpad.len == digest_size)
    _(invariant digestpad.val == (\lambda \natural i; i<digest_size? digest_pad[i] : (uint8_t)0))
    _(invariant alg>0 && alg <= 8)
    _(invariant (&inner)->alg == hmac_to_hash(alg))
    _(invariant (&inner_just_key)->alg == hmac_to_hash(alg))
    _(invariant (&outer)->alg == hmac_to_hash(alg))
    _(invariant \mine(&inner) && \mine(&outer) && \mine(&inner_just_key))
    _(invariant digest_size == digest_size_alg(alg))
    _(invariant hash_block_size >= 9)
    _(invariant block_size == block_size_alg(alg))
};

#define wrap_hmac_state(state) _(ghost switch(hmac_to_hash(state->alg)){ \
    case S2N_HASH_NONE: \
        _(assert 0) \
    break; \
    case S2N_HASH_MD5: \
        _(wrap &(&state->inner_just_key)->hash_ctx.md5) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.md5, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.md5) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.md5, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.md5) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.md5, &(&state->outer)->hash_ctx}) \
        break; \
    case S2N_HASH_SHA1: \
        _(wrap &(&state->inner_just_key)->hash_ctx.sha1) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha1, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.sha1) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha1, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.sha1) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.sha1, &(&state->outer)->hash_ctx}) \
    break; \
    case S2N_HASH_SHA224: \
        _(wrap &(&state->inner_just_key)->hash_ctx.sha224) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha224, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.sha224) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha224, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.sha224) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.sha224, &(&state->outer)->hash_ctx}) \
    break; \
    case S2N_HASH_SHA256: \
        _(wrap &(&state->inner_just_key)->hash_ctx.sha256) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha256, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.sha256) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha256, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.sha256) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.sha256, &(&state->outer)->hash_ctx}) \
    break; \
    case S2N_HASH_SHA384: \
        _(wrap &(&state->inner_just_key)->hash_ctx.sha384) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha384, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.sha384) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha384, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.sha384) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.sha384, &(&state->outer)->hash_ctx}) \
    break; \
    case S2N_HASH_SHA512: \
        _(wrap &(&state->inner_just_key)->hash_ctx.sha512) \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx.sha512, &(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx.sha512) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha512, &(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx.sha512) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx.sha512, &(&state->outer)->hash_ctx}) \
    break; \
    default: _(assert 0)}) \
    _(wrap &state->inner_just_key) \
    _(wrap &state->inner) \
    _(wrap &state->outer) \
    _(ghost state->\owns = {&state->inner_just_key, &state->inner, &state->outer}) \
    _(wrap state)

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

//REPLACE WITH SWITCH
_(def uint16_t block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE) return 0; 
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

_(def uint16_t hash_block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE) return 0; 
    if (alg == S2N_HMAC_MD5) return 64; 
    if (alg == S2N_HMAC_SHA1) return 64; 
    if (alg == S2N_HMAC_SHA224) return 64; 
    if (alg == S2N_HMAC_SHA256) return 64; 
    if (alg == S2N_HMAC_SHA384) return 128; 
    if (alg == S2N_HMAC_SHA512) return 128; 
    if (alg == S2N_HMAC_SSLv3_MD5) return 64; 
    if (alg == S2N_HMAC_SSLv3_SHA1) return 64; 
    else return 64; 
})

//REPLACE WITH SWITCH
_(def uint16_t digest_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE) return 0; 
    if (alg == S2N_HMAC_MD5) return MD5_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA1) return SHA_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA224) return SHA224_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA256) return SHA256_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA384) return SHA384_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SHA512) return SHA512_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SSLv3_MD5) return MD5_DIGEST_LENGTH; 
    if (alg == S2N_HMAC_SSLv3_SHA1) return SHA_DIGEST_LENGTH; 
    else return 64; 
})

//REPLACE WITH SWITCH
_(def s2n_hash_algorithm hmac_to_hash(s2n_hmac_algorithm alg)
{
    if (alg == S2N_HMAC_NONE) return 0; 
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

_(def \bool is_sslv3(s2n_hmac_algorithm alg)
{
    if (alg>=7 && alg<=8) return 1;
    else return 0; 
})

static int s2n_sslv3_mac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \extent_mutable(state))
    //_(requires alg == state->alg)
    _(requires is_sslv3(alg))
    _(requires state->block_size == block_size_alg(alg) && state->digest_size == digest_size_alg(alg))
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires state->currently_in_hash_block == 0)
    _(requires state->hash_block_size == 64)
    _(requires state->key == make_num((uint8_t *)key,klen))
    _(writes \extent(state))
    _(ensures \unchanged(state->alg))
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result ==> hashState(&state->inner,0) == hashState(&state->inner_just_key,0))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->key))
    _(decreases 0)
{
    _(ghost state->key.val = (\lambda \natural i; i<klen? ((uint8_t *)key)[i] : (uint8_t)0))
    _(ghost state->key.len = klen)
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;

    if (alg == S2N_HMAC_SSLv3_MD5) {
        hash_alg = S2N_HASH_MD5;
    }
    if (alg == S2N_HMAC_SSLv3_SHA1) {
        hash_alg = S2N_HASH_SHA1;
    }

    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==0x36){
        state->xor_pad[i] = 0x36;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(ghost state->xorpad.len = state->block_size)
    GUARD(s2n_hash_init(&state->inner_just_key, hash_alg));
    GUARD(s2n_hash_update(&state->inner_just_key, key, klen));
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));
    _(assert hashState(&state->inner_just_key,0) == concatenate(state->key,state->xorpad))
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==0x5c){
        state->xor_pad[i] = 0x5c;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(ghost state->xorpad.len = state->block_size)
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_init(&state->outer, hash_alg));
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, key, klen));
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(assert \wrapped_with_deep_domain(&state->outer))
    /* Copy inner_just_key to inner */
    hmac_state_destroy(state);
    return s2n_hmac_reset(state);
}

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    //_(requires \extent_mutable(state)) 
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires alg > 0 && alg <= 8)
    _(writes \extent(state))
    _(ensures !\result ==> hashState(&state->inner,0) == hashState(&state->inner_just_key,0))
    _(ensures \result <= 0)
    _(ensures !\result ==> \wrapped(state))
    _(ensures state->alg == alg)
    _(ensures state->key == make_num((uint8_t *)key,klen))
    _(decreases 0)
    ;

int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
{
    _(ghost state->key.val = (\lambda \natural i; i<klen? ((uint8_t *)key)[i] : (uint8_t)0))
    _(ghost state->key.len = klen)
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;
    state->currently_in_hash_block = 0;
    state->digest_size = 0;
    state->block_size = 64;
    state->hash_block_size = 64; 
    switch (alg) {
    case S2N_HMAC_NONE:
        _(assert 0)
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
    _(assert sizeof(state->xor_pad) >= state->block_size) //USER-ADDED
    _(assert sizeof(state->digest_pad) >= state->digest_size) //USER-ADDED
    //gte_check(sizeof(state->xor_pad), state->block_size);
    //gte_check(sizeof(state->digest_pad), state->digest_size);
    
    state->alg = alg;
    if (alg == S2N_HMAC_SSLv3_SHA1 || alg == S2N_HMAC_SSLv3_MD5) {
        return s2n_sslv3_mac_init(state, alg, key, klen);
    }
    GUARD(s2n_hash_init(&state->inner_just_key, hash_alg));
    _(assert hashState(&state->inner_just_key,0) == repeat((uint8_t)0,0))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_init(&state->outer, hash_alg));
    _(assert hashState(&state->outer,0) == repeat((uint8_t)0,0))
    uint32_t copied = klen; 
    if (klen > state->block_size) {
        _(ghost \state t = \now())
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        _(ghost \state y = \now())
        GUARD(s2n_hash_update(&state->outer, key, klen));
        //_(assert hashState(&state->outer,0) == concatenate(\at(y,hashState(&state->outer,0)),make_num((uint8_t *)key,klen)))
        //_(assert make_num((uint8_t *)key,klen) == state->key)
        //_(assert concatenate(repeat((uint8_t)0,0),state->key) == state->key)
        //_(assert hashState(&state->outer,0) == concatenate(repeat((uint8_t)0,0),make_num((uint8_t *)key,klen)))
        //_(assert hashState(&state->outer,0) == concatenate(repeat((uint8_t)0,0),state->key))
        _(assert hashState(&state->outer,0) == state->key)
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        GUARD(s2n_hash_digest(&state->outer, state->digest_pad, state->digest_size)); 
        //_(assert make_num(state->digest_pad,state->digest_size) == hashVal(state->key,hash_alg))
        _(ghost state->digestpad.len = state->digest_size)
        _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
        //_(assert make_num(state->digest_pad,state->digest_size) == state->digestpad)
        _(assert state->digestpad == hashVal(state->key,hmac_to_hash(state->alg)))
        _(assert state->digest_size ==> state->xor_pad != NULL)
        //_(assert make_num((uint8_t *)key,klen) == state->key)
        //memcpy_check(state->xor_pad, state->digest_pad, state->digest_size);
        memcpy(state->xor_pad, state->digest_pad, state->digest_size); //USER-ADDED
        _(ghost state->xorpad.val = (\lambda \natural i; i<state->digest_size? state->digestpad.val[i] : (uint8_t)0))
        _(ghost state->xorpad.len = state->block_size)
        copied = state->digest_size;
        _(assert state->xorpad == num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size))
    } else {
        _(ghost state->digestpad.len = state->digest_size)
        _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
        //memcpy_check(state->xor_pad, key, klen);
        _(assert state->key.len ==> state->xor_pad != NULL)
        memcpy(state->xor_pad, key, klen); //USER-ADDED
        _(ghost state->xorpad.val = (\lambda \natural i; i<state->key.len? ((uint8_t *)(key))[i] : (uint8_t)0))
        _(ghost state->xorpad.len = state->block_size)
        _(assert state->xorpad == num_resize(state->key,state->block_size))
    }
    _(assert state->key.len>state->block_size ==> state->xorpad == num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size))
    _(assert state->key.len<=state->block_size ==> state->xorpad == num_resize(state->key,state->block_size))
    _(ghost \state s = \now())
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(assert \wrapped_with_deep_domain(&state->outer))
    for (int i = 0; i < (int) copied; i++) 
        _(writes \array_range(state->xor_pad,copied))
        _(decreases (int)copied - i)
        _(invariant i>= 0 && i<= (int)copied)
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j] == \old(state->xor_pad[j]^(uint8_t)0x36))
        _(invariant \forall int j; j>=i && j<(int)copied ==> state->xor_pad[j] == \old(state->xor_pad[j]))
    {
        state->xor_pad[i] ^= 0x36;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<copied? state->xor_pad[i] : (uint8_t)0))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(assert \wrapped_with_deep_domain(&state->outer))
    for (int i = (int) copied; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(decreases state->block_size - i)
        _(invariant \forall int j; (j>=0 && j<(int)copied || j>=i && j<state->block_size) ==> \unchanged(state->xor_pad[j]))
        _(invariant \forall int j; j>=(int)copied && j<i ==> state->xor_pad[j]== (uint8_t)0x36)
        _(invariant i>=(int)copied && i<= state->block_size){
        state->xor_pad[i] = 0x36;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(assert \wrapped_with_deep_domain(&state->outer))
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));
    _(assert state->key.len<=state->block_size ==> hashState(&state->inner_just_key,0) == xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)))
    _(assert state->key.len>state->block_size ==> hashState(&state->inner_just_key,0) == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(assert \wrapped_with_deep_domain(&state->outer))
    for (int i = 0; i < state->block_size; i++) 
    _(writes \array_range(state->xor_pad,state->block_size))
    _(invariant i>=0 && i <= state->block_size)
    _(decreases state->block_size - i)
    _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j] == \old(state->xor_pad[j]^(uint8_t)0x6a))
    _(invariant \forall int j; j>=i && j<state->block_size ==> state->xor_pad[j] == \old(state->xor_pad[j]))
    {
        state->xor_pad[i] ^= 0x6a;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(ghost if(state->key.len<=state->block_size){_(ghost xor_combine(0x36,0x6a, num_resize(state->key,state->block_size)))}
    else{_(ghost xor_combine(0x36,0x6a, num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size)))})
    _(assert state->key.len>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat((uint8_t)(0x36^0x6a),state->block_size)))
    _(assert state->key.len>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)))
    //AS EXPECTED THIS FAILS_(assert state->key.len>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5b,state->block_size)))
    _(assert state->key.len<=state->block_size ==> state->xorpad == xor(num_resize(state->key,state->block_size),repeat((uint8_t)(0x36^0x6a),state->block_size)))
    _(assert state->key.len<=state->block_size ==> state->xorpad == xor(num_resize(state->key,state->block_size),repeat(0x5c,state->block_size)))
    _(assert hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(assert state->key.len<=state->block_size ==> hashState(&state->inner_just_key,0) == xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)))
    _(assert state->key.len>state->block_size ==> hashState(&state->inner_just_key,0) == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    /*hmac_state_destroy2(state);
    _(assert state->key.len>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5b,state->block_size)))
    */
    //_(assert \wrapped_with_deep_domain(&state->outer))
    //_(assert \wrapped_with_deep_domain(&state->inner_just_key))
    //hash_state_destroy2(&state->inner);
    //_(assert \wrapped_with_deep_domain(&state->outer))
    //hash_state_destroy(&state->inner_just_key);
    //hash_state_destroy(&state->outer);
    //_(assert state->key.len>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)))
    //hmac_state_destroy4(state);
        
        
        //_(assert \wrapped_with_deep_domain(&state->outer))
    //hash_state_destroy(&state->inner_just_key);
    //_(assert \wrapped_with_deep_domain(&state->inner_just_key))
    //hash_state_destroy(&state->outer);
    /*_(assert klen>state->block_size ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)))
    _(ghost state->\owns = {&state->inner, &state->outer, &state->inner_just_key})
    _(assert state->key.len <= state->block_size &&    !is_sslv3(state->alg)  ==> hashState(&state->inner_just_key,0) == xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)))
    _(assert state->key.len > state->block_size &&     !is_sslv3(state->alg)  ==> hashState(&state->inner_just_key,0) == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    _(assert                             !is_sslv3(state->alg)  ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(assert                             is_sslv3(state->alg)   ==> hashState(&state->inner_just_key,0) == concatenate(state->key,repeat(0x36,state->block_size)))
    _(assert                             is_sslv3(state->alg) ==> hashState(&state->outer,0) == concatenate(state->key,repeat(0x5c,state->block_size)))
    _(assert valid(state->xorpad))
    _(assert state->xorpad.len == state->block_size)
    _(assert state->xorpad.val == (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(assert state->key.len>state->block_size && !is_sslv3(state->alg) ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)))
    _(assert state->key.len<=state->block_size && !is_sslv3(state->alg) ==> state->xorpad == xor(num_resize(state->key,state->block_size),repeat(0x5c,state->block_size)))
    _(assert is_sslv3(state->alg) ==> state->xorpad == repeat((uint8_t)0x5c,state->block_size))
    _(assert valid(state->digestpad))
    _(assert state->digestpad.len == state->digest_size)
    _(assert state->digestpad.val == (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
    _(assert state->alg>0 && state->alg <= 8)
    _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
    _(assert state->digest_size == digest_size_alg(state->alg))
    _(assert state->hash_block_size >= 9)
    _(assert state->block_size == block_size_alg(state->alg))*/
    return s2n_hmac_reset(state);
}  

extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(requires \wrapped(state))
    _(requires \thread_local_array((uint8_t *)in,size))
    //_(requires state->currently_in_hash_block + (4294949760 + size) % state->hash_block_size <= _UI32_MAX - SYSTEM_PAGE_SIZE())
    _(writes state)
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result ==> hashState(&state->inner,0) == concatenate(\old(hashState(&state->inner,0)),make_num((uint8_t *)in,size)))
    _(ensures \unchanged(state->digestpad))
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(state->key))
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
    _(unchecked)(state->currently_in_hash_block += ((4294949760 + size) % state->hash_block_size));
    state->currently_in_hash_block %= state->block_size;
    {
        _(assert \wrapped_with_deep_domain(&state->inner_just_key)) 
        _(assert \wrapped_with_deep_domain(&state->outer))
        int res = s2n_hash_update(&state->inner, in, size);
        _(wrap state) 
        return res; 
    }
}

static int s2n_sslv3_mac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires state->alg >= 7 && state->alg <= 8)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires \thread_local_array((uint8_t *)outt,size))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures !\result ==> \wrapped(state) && \thread_local_array((uint8_t *)outt,size))
    _(ensures \unchanged(state->hash_block_size))
    _(ensures \result <= 0)
    _(ensures !\result ==> hashState(&state->inner,0)==repeat((uint8_t)0,0))
    _(ensures !\result ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(\old(hashState(&state->outer,0)),state->digestpad),hmac_to_hash(state->alg)))
    _(ensures !\result ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures !\result ==> \unchanged(hashState(&state->outer,0)))
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(state->currently_in_hash_block))
    _(ensures \unchanged(hashState(&state->inner_just_key,0)))
{
    _(unwrap state)
    _(assert \wrapped_with_deep_domain(&state->inner))
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==(uint8_t)0x5c)
        _(invariant i>=0 && i<=state->block_size){
        state->xor_pad[i] = (uint8_t)0x5c;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(ghost \state s= \now())
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    //memcpy/*_check*//*(&state->inner, &state->outer, sizeof(state->inner));
    _(wrap state)
    hmac_state_destroy(state);
    state->inner = state->outer; //USER ADDED INSTEAD OF MEMCPY
    wrap_hmac_state(state);
    _(unwrap state)
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->inner, state->digest_pad, state->digest_size));
    _(assert hashState(&state->inner,0) == concatenate(\at(s,hashState(&state->outer,0)),state->digestpad))
    {
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res= s2n_hash_digest(&state->inner, outt, size);
        _(wrap state)
        return res;
    }
}

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(maintains \thread_local_array((uint8_t *)outt,size))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures \unchanged(state->alg))
    _(ensures !\result ==> \wrapped(state))
    _(ensures \unchanged(state->currently_in_hash_block))
    _(ensures !is_sslv3(state->alg) ==> \unchanged(state->xorpad))
    _(ensures !\result && !is_sslv3(state->alg) ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures !\result && !is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size)==hashVal(concatenate(state->xorpad,state->digestpad),hmac_to_hash(state->alg)))  
    _(ensures !\result && !is_sslv3(state->alg) ==> hashState(&state->inner,0) == repeat((uint8_t)0,0))
    _(ensures !\result && is_sslv3(state->alg) ==> hashState(&state->inner,0) == repeat((uint8_t)0,0))
    _(ensures !\result && is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(\old(hashState(&state->outer,0)),state->digestpad),hmac_to_hash(state->alg)))
    _(ensures !\result && is_sslv3(state->alg) ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures \unchanged(state->key))
    _(ensures \result <= 0)
;

int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    if (state->alg == S2N_HMAC_SSLv3_SHA1 || state->alg == S2N_HMAC_SSLv3_MD5) {
        return s2n_sslv3_mac_digest(state, outt, size);
    }
    _(unwrap state)
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_reset(&state->outer));
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->digest_pad, state->digest_size));
    _(assert state->alg && !is_sslv3(state->alg) ==> hashState(&state->outer,0) == concatenate(concatenate(repeat((uint8_t)0,0),state->xorpad),state->digestpad))  
    { 
        _(assert \wrapped_with_deep_domain(&state->inner))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res = s2n_hash_digest(&state->outer,outt, size);
        _(wrap state)
        return res; 
    }
}

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires !is_sslv3(state->alg))
    _(requires \thread_local_array((uint8_t *)outt,size))
    _(writes state, \array_range(_(uint8_t *)outt,size))
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result && state->alg && !is_sslv3(state->alg) ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures !\result && state->alg && !is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size)==hashVal(concatenate(concatenate(repeat((uint8_t)0,0),state->xorpad),state->digestpad),hmac_to_hash(state->alg)))  
    _(ensures !\result && state->alg && !is_sslv3(state->alg) ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(ensures !\result && !is_sslv3(state->alg) && state->currently_in_hash_block <= (state->hash_block_size - 9) ==> hashState(&state->inner,0) == make_num(state->xor_pad,state->hash_block_size))
    _(ensures !\result && !is_sslv3(state->alg) && state->currently_in_hash_block > (state->hash_block_size - 9) ==> hashState(&state->inner,0) == repeat((uint8_t)0,0))
    _(ensures !\result && is_sslv3(state->alg) && (state->currently_in_hash_block <= (state->hash_block_size - 9)) ==> hashState(&state->inner,0) == make_num(state->xor_pad,state->hash_block_size))
    _(ensures !\result && is_sslv3(state->alg) && (state->currently_in_hash_block > (state->hash_block_size - 9)) ==> hashState(&state->inner,0) == repeat((uint8_t)0,0))
    _(ensures !\result && is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(\old(hashState(&state->outer,0)),state->digestpad),hmac_to_hash(state->alg)))
    _(ensures !\result && is_sslv3(state->alg) ==> state->digestpad == hashVal(\old(hashState(&state->inner,0)),hmac_to_hash(state->alg)))
    _(ensures !\result && is_sslv3(state->alg) ==> \unchanged(hashState(&state->outer,0)))
    _(ensures \unchanged(hashState(&state->inner_just_key,0)))
    _(ensures !\result && is_sslv3(state->alg) ==> state->xorpad == repeat((uint8_t)0x5c,state->block_size))
    _(ensures !\result && !is_sslv3(state->alg) ==> \unchanged(state->xorpad))
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
    _(assert state->alg && !is_sslv3(state->alg) ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))

    _(unwrap state)
    _(assert state->alg && !is_sslv3(state->alg) ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(ghost \state s=\now())
    { 
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        _(assert \thread_local_array(state->xor_pad,state->block_size))
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
    //_(requires \extent_mutable(state))
    _(requires \mutable(state) && \extent_mutable(&state->inner) && \wrapped(&state->inner_just_key) && \wrapped(&state->outer))
    //_(requires \inv(state) && \inv(&state->inner) && \inv(&state->outer) && \inv(&state->inner_just_key))
        _(requires state->key.len <= state->block_size &&    !is_sslv3(state->alg)  ==> hashState(&state->inner_just_key,0) == xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)))
    _(requires state->key.len > state->block_size &&     !is_sslv3(state->alg)  ==> hashState(&state->inner_just_key,0) == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    _(requires                             !is_sslv3(state->alg)  ==> hashState(&state->outer,0) == repeat((uint8_t)0,0))
    _(requires                             is_sslv3(state->alg)   ==> hashState(&state->inner_just_key,0) == concatenate(state->key,repeat(0x36,state->block_size)))
    _(requires                             is_sslv3(state->alg) ==> hashState(&state->outer,0) == concatenate(state->key,repeat(0x5c,state->block_size)))
    _(requires valid(state->xorpad))
    _(requires state->xorpad.len == state->block_size)
    _(requires state->xorpad.val == (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0))
    _(requires state->key.len>state->block_size && !is_sslv3(state->alg) ==> state->xorpad == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)))
    _(requires state->key.len<=state->block_size && !is_sslv3(state->alg) ==> state->xorpad == xor(num_resize(state->key,state->block_size),repeat(0x5c,state->block_size)))
    _(requires is_sslv3(state->alg) ==> state->xorpad == repeat((uint8_t)0x5c,state->block_size))
    _(requires valid(state->digestpad))
    _(requires state->digestpad.len == state->digest_size)
    _(requires state->digestpad.val == (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0))
    _(requires state->alg>0 && state->alg <= 8)
    _(requires (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    _(requires (&state->outer)->alg == hmac_to_hash(state->alg))
    _(requires state->digest_size == digest_size_alg(state->alg))
    _(requires state->hash_block_size == hash_block_size_alg(state->alg))
    _(requires state->block_size == block_size_alg(state->alg))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_MD5 ==> \union_active(&(&state->outer)->hash_ctx.md5) && \union_active(&(&state->inner_just_key)->hash_ctx.md5))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA1 ==> \union_active(&(&state->outer)->hash_ctx.sha1) && \union_active(&(&state->inner_just_key)->hash_ctx.sha1))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA224 ==> \union_active(&(&state->outer)->hash_ctx.sha224) && \union_active(&(&state->inner_just_key)->hash_ctx.sha224))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA256 ==> \union_active(&(&state->outer)->hash_ctx.sha256) && \union_active(&(&state->inner_just_key)->hash_ctx.sha256))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA384 ==> \union_active(&(&state->outer)->hash_ctx.sha384) && \union_active(&(&state->inner_just_key)->hash_ctx.sha384))
    _(requires hmac_to_hash(state->alg) == S2N_HASH_SHA512 ==> \union_active(&(&state->outer)->hash_ctx.sha512) && \union_active(&(&state->inner_just_key)->hash_ctx.sha512))
    _(writes \span(state), \extent(&state->inner), &state->inner_just_key, &state->outer)
    _(ensures hashState(&state->inner,0)== hashState(&state->inner_just_key,0))
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(state->key))
    _(ensures \wrapped(state))
    _(ensures \result <= 0)
    _(decreases 0) 
;

int s2n_hmac_reset(struct s2n_hmac_state *state)
{
    state->currently_in_hash_block = 0;
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    _(assert \wrapped_with_deep_domain(&state->outer))
    hash_state_destroy(&state->inner_just_key);
    hash_state_destroy(&state->outer);
    //memcpy_check(&state->inner, &state->inner_just_key, sizeof(state->inner));
    state->inner = state->inner_just_key; //USER ADDED

    wrap_hmac_state(state);
    _(assert 0)
    return 0;
}

int hmac_state_destroy(struct s2n_hmac_state *s)
    _(requires \wrapped(s) || \mutable(s))
    _(writes s)
    _(ensures s->digestpad.val == (\lambda \natural i; i<s->digest_size? s->digest_pad[i]:(uint8_t)0))
    _(ensures s->xorpad.val == (\lambda \natural i; i<s->block_size? s->xor_pad[i]:(uint8_t)0))
    _(ensures \unchanged(s->digestpad) && \unchanged(s->xorpad) && \unchanged(s->digest_size) && \unchanged(s->block_size))
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
    _(ensures \unchanged(hashState(&s->inner,0)) && valid(hashState(&s->inner,0)))
    _(ensures \unchanged(hashState(&s->outer,0)) && valid(hashState(&s->outer,0)))
    _(ensures \unchanged(hashState(&s->inner_just_key,0)) && valid(hashState(&s->inner_just_key,0)))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_MD5 ==> \union_active(&(&s->inner)->hash_ctx.md5) && \union_active(&(&s->outer)->hash_ctx.md5) && \union_active(&(&s->inner_just_key)->hash_ctx.md5))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA1 ==> \union_active(&(&s->inner)->hash_ctx.sha1) && \union_active(&(&s->outer)->hash_ctx.sha1) && \union_active(&(&s->inner_just_key)->hash_ctx.sha1))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA224 ==> \union_active(&(&s->inner)->hash_ctx.sha224) && \union_active(&(&s->outer)->hash_ctx.sha224) && \union_active(&(&s->inner_just_key)->hash_ctx.sha224))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA256 ==> \union_active(&(&s->inner)->hash_ctx.sha256) && \union_active(&(&s->outer)->hash_ctx.sha256) && \union_active(&(&s->inner_just_key)->hash_ctx.sha256))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA384 ==> \union_active(&(&s->inner)->hash_ctx.sha384) && \union_active(&(&s->outer)->hash_ctx.sha384) && \union_active(&(&s->inner_just_key)->hash_ctx.sha384))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA512 ==> \union_active(&(&s->inner)->hash_ctx.sha512) && \union_active(&(&s->outer)->hash_ctx.sha512) && \union_active(&(&s->inner_just_key)->hash_ctx.sha512))
    _(ensures \unchanged(s->key))
    _(ensures \unchanged(hashVal(s->key,hmac_to_hash(s->alg))))
    _(decreases 0)
;

int hmac_state_destroy4(struct s2n_hmac_state *s)
    _(requires \mutable(s))
    _(writes \extent(s))
    _(ensures s->digestpad.val == (\lambda \natural i; i<s->digest_size? s->digest_pad[i]:(uint8_t)0))
    _(ensures s->xorpad.val == (\lambda \natural i; i<s->block_size? s->xor_pad[i]:(uint8_t)0))
    _(ensures \unchanged(s->digestpad) && \unchanged(s->xorpad) && \unchanged(s->digest_size) && \unchanged(s->block_size))
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
    _(ensures \unchanged(hashState(&s->inner,0)) && valid(hashState(&s->inner,0)))
    _(ensures \unchanged(hashState(&s->outer,0)) && valid(hashState(&s->outer,0)))
    _(ensures \unchanged(hashState(&s->inner_just_key,0)) && valid(hashState(&s->inner_just_key,0)))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_MD5 ==> \union_active(&(&s->inner)->hash_ctx.md5) && \union_active(&(&s->outer)->hash_ctx.md5) && \union_active(&(&s->inner_just_key)->hash_ctx.md5))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA1 ==> \union_active(&(&s->inner)->hash_ctx.sha1) && \union_active(&(&s->outer)->hash_ctx.sha1) && \union_active(&(&s->inner_just_key)->hash_ctx.sha1))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA224 ==> \union_active(&(&s->inner)->hash_ctx.sha224) && \union_active(&(&s->outer)->hash_ctx.sha224) && \union_active(&(&s->inner_just_key)->hash_ctx.sha224))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA256 ==> \union_active(&(&s->inner)->hash_ctx.sha256) && \union_active(&(&s->outer)->hash_ctx.sha256) && \union_active(&(&s->inner_just_key)->hash_ctx.sha256))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA384 ==> \union_active(&(&s->inner)->hash_ctx.sha384) && \union_active(&(&s->outer)->hash_ctx.sha384) && \union_active(&(&s->inner_just_key)->hash_ctx.sha384))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA512 ==> \union_active(&(&s->inner)->hash_ctx.sha512) && \union_active(&(&s->outer)->hash_ctx.sha512) && \union_active(&(&s->inner_just_key)->hash_ctx.sha512))
    _(ensures \unchanged(s->key))
    _(ensures \unchanged(hashVal(s->key,hmac_to_hash(s->alg))))
    _(decreases 0)
;

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(requires \wrapped(from))
    _(requires \extent_mutable(to))
    _(requires from != to)
    _(writes \extent(to), from)
    _(ensures \wrapped(to))
    _(ensures \result <= 0)
    _(ensures hashState(&to->inner,0) == \old(hashState(&from->inner,0)))
    _(ensures hashState(&to->inner_just_key,0) == \old(hashState(&from->inner_just_key,0)))
    _(ensures hashState(&to->outer,0) == \old(hashState(&from->outer,0)))
    _(ensures \unchanged(hashState(&from->inner,0)))
; 

int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
{
    _(assert sizeof(struct s2n_hmac_state) ==> to != NULL)
    //memcpy_check(to, from, sizeof(struct s2n_hmac_state));
    hmac_state_destroy(from);
    *to = *from; //USED ADDED IN PLACE OF MEMCPY
    wrap_hmac_state(to);
    return 0;
}

int testing(uint8_t *data, uint32_t size, uint8_t *data1, uint32_t size1, uint8_t *data2, uint32_t size2)
    //_(requires \thread_local_array(data,size))
    _(requires size)
    _(requires size1)
    _(requires size2==20)
    _(requires \arrays_disjoint(data,size,data1,size1) && \arrays_disjoint(data1,size1,data2,size2) && \arrays_disjoint(data,size,data2,size2))
    _(writes \array_range(data,size))
    _(writes \array_range(data1,size1))
    _(writes \array_range(data2,size2))
{
    struct s2n_blob *key = malloc(sizeof(*key));
    if(key==NULL) return -1;
    s2n_blob_init(key,data,size);
    struct s2n_blob *b = malloc(sizeof(*b));
    if(b==NULL) return -1;
    s2n_blob_init(b,data1,size1);
    struct s2n_blob *outt = malloc(sizeof(*outt));
    if(outt==NULL) return -1;
    s2n_blob_init(outt,data2,size2);
    struct s2n_hash_state *s = malloc(sizeof(*s));
    if(s==NULL) return -1;
    s2n_hash_algorithm t = S2N_HASH_SHA1;
    s2n_hash_init(s,t);
    struct s2n_hmac_state *state = malloc(sizeof(*state));
    if(state==NULL) return -1;
    //_(unwrap key)
    s2n_hmac_algorithm r = S2N_HMAC_SHA1;
    GUARD(s2n_hmac_init(state,r,key->data,key->size)); //\wrapped(\domain_root(\embedding((uint8_t*)key))) fails. If I unwrap key, I get unreachable code
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> hashState(&state->inner,0)== xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    GUARD(s2n_hmac_update(state,b->data,b->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> hashState(&state->inner,0)==concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)),make_num(b->data,b->size)))
    GUARD(s2n_hmac_digest(state,outt->data,outt->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> make_num(outt->data,outt->size) == hashVal(concatenate(xor(num_resize(hashVal(make_num(key->data,key->size),hmac_to_hash(r)),block_size_alg(r)),repeat(0x5c,block_size_alg(r))),hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)),make_num(b->data,b->size)),hmac_to_hash(r))),hmac_to_hash(r)))
}


