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
//#include <stdio.h>
#include <stdlib.h>
//#include "myblob.h"

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
    _(ghost \bool valid)
    _(invariant valid == (&inner)->valid)
    _(invariant (&inner_just_key)->valid)
    _(invariant is_sslv3(alg) ==> (&outer)->valid)
    _(ghost Num key)
    _(ghost Num message)
    _(invariant valid_num(message))
    _(invariant valid ==> concatenate((&inner_just_key)->hashState,message) == (&inner)->hashState)
    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;

    _(invariant key.len <= block_size && alg && !is_sslv3(alg)  ==> (&inner_just_key)->hashState == xor(num_resize(key,block_size),repeat(0x36,block_size)))
    _(invariant key.len > block_size && alg && !is_sslv3(alg)  ==> (&inner_just_key)->hashState == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x36,block_size)))
    _(invariant !alg ==> (&inner_just_key)->hashState == repeat(0x0,0))
    _(invariant                             !is_sslv3(alg)  ==> (&outer)->hashState == repeat(0x0,0))
    _(invariant                             is_sslv3(alg)   ==> (&inner_just_key)->hashState == concatenate(key,repeat(0x36,block_size)))
    _(invariant                             is_sslv3(alg) ==> (&outer)->hashState == concatenate(key,repeat(0x5c,block_size)))
    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];
    _(ghost Num xorpad)
    _(invariant xorpad == make_num(xor_pad,block_size))
    _(invariant key.len>block_size && alg && !is_sslv3(alg) ==> xorpad == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x5c,block_size)))
    _(invariant key.len>block_size && !alg && !is_sslv3(alg) ==> xorpad == repeat(0x5c,block_size))
    _(invariant key.len<=block_size && !is_sslv3(alg) ==> xorpad == xor(num_resize(key,block_size),repeat(0x5c,block_size)))
    _(invariant is_sslv3(alg) ==> xorpad == repeat(0x5c,block_size))
    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
    _(ghost Num digestpad)
    _(invariant digestpad == make_num(digest_pad,digest_size))
    _(invariant alg>=0 && alg <= 8)
    _(invariant (&inner)->alg == hmac_to_hash(alg))
    _(invariant (&inner_just_key)->alg == hmac_to_hash(alg))
    _(invariant (&outer)->alg == hmac_to_hash(alg))
    _(invariant \mine(&inner) && \mine(&outer) && \mine(&inner_just_key))
    _(invariant digest_size == digest_size_alg(alg))
    _(invariant hash_block_size == hash_block_size_alg(alg))
    _(invariant block_size == block_size_alg(alg))
};

#define wrap_hmac_state(state) {switch(hmac_to_hash(state->alg)){ \
    case S2N_HASH_NONE: \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx}) \
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
    default: _(assert 0)} \
    _(wrap &state->inner_just_key) \
    _(wrap &state->inner) \
    _(wrap &state->outer) \
    _(ghost state->\owns = {&state->inner_just_key, &state->inner, &state->outer}) \
    _(wrap state)}

#define wrap_hash_states(state) {switch(hmac_to_hash(state->alg)){ \
    case S2N_HASH_NONE: \
        _(wrap &(&state->inner_just_key)->hash_ctx) \
        _(ghost (&state->inner_just_key)->\owns = {&(&state->inner_just_key)->hash_ctx}) \
        _(wrap &(&state->inner)->hash_ctx) \
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx}) \
        _(wrap &(&state->outer)->hash_ctx) \
        _(ghost (&state->outer)->\owns = {&(&state->outer)->hash_ctx}) \
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
    default: _(assert 0)} \
    _(wrap &state->inner_just_key) \
    _(wrap &state->inner) \
    _(wrap &state->outer) \
    _(ghost state->\owns = {&state->inner_just_key, &state->inner, &state->outer})}

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
    if (alg == S2N_HMAC_NONE || alg == S2N_HMAC_SHA224 || alg == S2N_HMAC_SHA256) return 64; 
    if (alg == S2N_HMAC_MD5 || alg == S2N_HMAC_SSLv3_MD5) return 48; 
    if (alg == S2N_HMAC_SHA1 || alg == S2N_HMAC_SSLv3_SHA1) return 40; 
    if (alg == S2N_HMAC_SHA384 || alg == S2N_HMAC_SHA512) return 128; 
    else return 64; 
})

_(def uint16_t hash_block_size_alg(s2n_hmac_algorithm alg) 
{ 
    if (alg == S2N_HMAC_NONE || alg == S2N_HMAC_MD5 || alg == S2N_HMAC_SHA1 || alg == S2N_HMAC_SHA224 || alg == S2N_HMAC_SHA256 || alg == S2N_HMAC_SSLv3_MD5 || alg == S2N_HMAC_SSLv3_SHA1) return 64; 
    if (alg == S2N_HMAC_SHA384 || alg == S2N_HMAC_SHA512) return 128; 
    else return 64; 
})

//REPLACE WITH SWITCH
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

//REPLACE WITH SWITCH
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
    else return S2N_HASH_NONE; //CAN I REMOVE THIS?
})

_(def \bool is_sslv3(s2n_hmac_algorithm alg)
{
    if (alg>=7 && alg<=8) return 1;
    else return 0; 
})

_(def \bool is_valid_hmac(s2n_hmac_algorithm alg)
{
    if (alg>=0 && alg<=8) return 1;
    else return 0; 
})

static int s2n_sslv3_mac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \extent_mutable(state))
    _(requires is_sslv3(alg))
    _(requires state->block_size == block_size_alg(alg) && state->digest_size == digest_size_alg(alg))
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires state->currently_in_hash_block == 0)
    _(requires state->hash_block_size == hash_block_size_alg(alg))
    _(requires state->key == make_num((uint8_t *)key,klen))
    _(writes \extent(state))
    _(ensures \unchanged(state->alg))
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result ==> state->message == repeat(0x0,0))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->key))
    _(ensures state->valid)
    _(decreases 0)
{
    _(ghost state->key.val = (\lambda \natural i; i<klen? ((uint8_t *)key)[i] : (uint8_t)0x0))
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
    //WRITE AS MAKE_NUM
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0x0))
    _(ghost state->xorpad.len = state->block_size)
    GUARD(s2n_hash_init(&state->inner_just_key, hash_alg));
    GUARD(s2n_hash_update(&state->inner_just_key, key, klen));
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));
    _(assert (&state->inner_just_key)->hashState == concatenate(state->key,state->xorpad))
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==0x5c){
        state->xor_pad[i] = 0x5c;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0x0))
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
    _(ghost hmac_state_destroy(state);)
    return s2n_hmac_reset(state);
}

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires is_valid_hmac(alg))
    _(writes \extent(state))
    _(ensures !\result ==> state->message == repeat(0x0,0))
    _(ensures \result <= 0)
    _(ensures !\result ==> \wrapped(state))
    _(ensures state->alg == alg)
    _(ensures state->key == make_num((uint8_t *)key,klen))
    _(ensures !\result ==> state->valid)
    _(decreases 0)
    ;

int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
{
    //WRITE USING BLOCK CONTRACTS
    //put initial wrapping in a ghost function
    //_(isolate proof)
    // /b:/restartProver
    _(ghost xor_ass())
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;
    state->currently_in_hash_block = 0;
    state->digest_size = 0;
    state->block_size = 64;
    state->hash_block_size = 64; 
    switch (alg) {
    case S2N_HMAC_NONE:
        //_(assert make_num(state->digest_pad,state->digest_size) == repeat(0x0,0))
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
        _(ghost state->key = make_num((uint8_t *)key,klen))
        return s2n_sslv3_mac_init(state, alg, key, klen);
    }
    _(assert sizeof(state->xor_pad) >= state->block_size) //USER-ADDED
    _(assert sizeof(state->digest_pad) >= state->digest_size) //USER-ADDED
    //gte_check(sizeof(state->xor_pad), state->block_size);
    //gte_check(sizeof(state->digest_pad), state->digest_size);

    _(requires hash_alg == hmac_to_hash(alg))
    _(writes \extent(&state->inner_just_key), \extent(&state->outer), \extent(&state->inner))
    _(ensures \wrapped(&state->outer) && \wrapped(&state->inner_just_key) && \wrapped(&state->inner))
    _(ensures (&state->outer)->alg == hmac_to_hash(alg))
    _(ensures (&state->inner_just_key)->alg == hmac_to_hash(alg))
    _(ensures (&state->outer)->valid && (&state->inner_just_key)->valid)
    _(ensures (&state->outer)->hashState == repeat(0x0,0))
    _(ensures (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(ensures (&state->outer)->real && (&state->inner_just_key)->real)
    {
        s2n_hash_init(&state->outer, hash_alg);
        s2n_hash_init(&state->inner_just_key, hash_alg);
        _(ghost (&state->inner)->real = 0)
        _(wrap &(&state->inner)->hash_ctx) 
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx}) 
        _(wrap (&state->inner))
    }
    
    uint32_t copied = klen;

    if (klen > state->block_size) {
        s2n_hash_update(&state->outer, key, klen);
        _(assert state->alg ==> (&state->outer)->hashState == make_num((uint8_t*)key,klen))
        _(assert !state->alg ==> (&state->outer)->hashState == repeat(0x0,0))
        s2n_hash_digest(&state->outer, state->digest_pad, state->digest_size); 
        _(assert !state->alg ==> make_num(state->digest_pad,state->digest_size) == repeat(0x0,0))
        //memcpy_check(state->xor_pad, state->digest_pad, state->digest_size);
        memcpy(state->xor_pad, state->digest_pad, state->digest_size); //USER-ADDED
        copied = state->digest_size;
    } else {
        //memcpy_check(state->xor_pad, key, klen);
        memcpy(state->xor_pad, key, klen); //USER-ADDED
    }
    
    _(assert state->alg && klen>state->block_size ==> make_num(state->xor_pad,copied) == hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)))
    _(assert !state->alg && klen>state->block_size ==> make_num(state->xor_pad,copied) == repeat(0x0,0))
    _(assert klen<=state->block_size ==> make_num(state->xor_pad,copied) == make_num((uint8_t *)key,klen))

    _(ghost xor_ass())
    _(ghost \state t = \now())
    
    for (int i = 0; i < (int) copied; i++) 
        _(writes \array_range(state->xor_pad,copied))
        _(invariant i>= 0 && i<= (int)copied)
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j] == \old(state->xor_pad[j]^(uint8_t)0x36))
        _(invariant \forall int j; j>=i && j<(int)copied ==> state->xor_pad[j] == \old(state->xor_pad[j]))
    {
        state->xor_pad[i] ^= 0x36;
    }
    for (int i = (int) copied; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; (j>=0 && j<(int)copied || j>=i && j<state->block_size) ==> \unchanged(state->xor_pad[j]))
        _(invariant \forall int j; j>=(int)copied && j<i ==> state->xor_pad[j]== 0x36)
        _(invariant i>=(int)copied && i<= state->block_size){
        state->xor_pad[i] = 0x36;
    }
    
    s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size);

    for (int i = 0; i < state->block_size; i++) 
    _(writes \array_range(state->xor_pad,state->block_size))
    _(invariant i>=0 && i <= state->block_size)
    _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j] == \old(state->xor_pad[j]^(uint8_t)0x6a))
    _(invariant \forall int j; j>=i && j<state->block_size ==> state->xor_pad[j] == \old(state->xor_pad[j]))
    {
        state->xor_pad[i] ^= 0x6a;
    }
    
    _(assert make_num(state->xor_pad,block_size_alg(alg)) == xor(num_resize(\at(t,make_num(state->xor_pad,copied)),block_size_alg(alg)),repeat((uint8_t)(0x36^0x6a),block_size_alg(alg))))
    _(assert make_num(state->xor_pad,block_size_alg(alg)) == xor(num_resize(\at(t,make_num(state->xor_pad,copied)),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    
    _(assert make_num((uint8_t *)key,klen) == \at(t,make_num((uint8_t *)key,klen)))
    _(assert alg && klen>block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    _(assert !alg && klen>block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == repeat(0x5c,block_size_alg(alg)))
    _(assert klen<=block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    _(assert alg && klen>block_size_alg(alg) ==> (&state->inner_just_key)->hashState == xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(state->alg)),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(assert !alg ==> (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(assert alg && klen<=block_size_alg(alg) ==> (&state->inner_just_key)->hashState == xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    
    _(ghost state->key = make_num((uint8_t *)key,klen))
    _(ghost state->xorpad = make_num(state->xor_pad,block_size_alg(alg)))
    _(ghost state->digestpad = make_num(state->digest_pad,digest_size_alg(alg)))

    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires !((uint8_t*)key \in \domain(&state->inner)) && !((uint8_t*)key \in \domain(&state->inner_just_key)))
    _(ensures (&state->inner)->alg == hmac_to_hash(alg))
    _(maintains (&state->inner_just_key)->alg == hmac_to_hash(alg))
    _(maintains \wrapped(&state->inner_just_key) && \wrapped(&state->inner))
    _(maintains (&state->inner_just_key)->valid && (&state->inner_just_key)->real)
    _(ensures (&state->inner)->valid && (&state->inner)->real)
    _(maintains alg && klen>block_size_alg(alg) ==> (&state->inner_just_key)->hashState == xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(maintains !alg ==> (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(maintains alg && klen<=block_size_alg(alg) ==> (&state->inner_just_key)->hashState == xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(ensures alg && klen>block_size_alg(alg) ==> (&state->inner)->hashState == xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(ensures !alg ==> (&state->inner)->hashState == repeat(0x0,0))
    _(ensures alg && klen<=block_size_alg(alg) ==> (&state->inner)->hashState == xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg)))) 
    _(writes &state->inner_just_key,&state->inner)
    {
        _(ghost \state t = \now())
        _(ghost hash_state_destroy(&state->inner_just_key);)
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
        _(ghost hash_state_destroy(&state->inner))
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
/*NOTE: IN THE ORIGINAL CODE, THE FUNCTION RETURNS S2N_HMAC_RESET. AS ALL THAT FUNCTION DOES IS COPY S2N_HMAC_INNER_JUST_KEY
TO S2N_HMAC_INNER, WE HAVE COPIED THAT COMMAND AT THE END OF THIS FUNCTION TO AVOID THE EXTREMELY LENGTHY PRECONDITIONS
THAT WOULD HAVE RESULTED.*/
        state->inner = state->inner_just_key;
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
        _(ghost wrap_hash_state((&state->inner)))
        _(ghost wrap_hash_state((&state->inner_just_key)))
        _(wrap (&state->inner))
        _(wrap (&state->inner_just_key))
    }
        
    _(ghost state->message = repeat(0x0,0))
    _(ghost state->valid = (&state->inner)->valid)
    _(wrap state)
    
    return 0;
}
  
extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(maintains \wrapped(state))
    _(maintains state->valid)
    _(requires \thread_local_array((uint8_t *)in,size))
    _(writes state)
    _(ensures !\result && state->alg ==> state->message == concatenate(\old(state->message),make_num((uint8_t *)in,size)))
    _(ensures !\result && !state->alg ==> state->message == repeat(0x0,0))
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
    _(assert \wrapped_with_deep_domain(state))
    _(unwrap state)
    _(unchecked)(state->currently_in_hash_block += ((4294949760 + size) % state->hash_block_size));
    state->currently_in_hash_block %= state->block_size;
    {
        _(assert \wrapped_with_deep_domain(&state->inner_just_key)) 
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(assert concatenate((&state->inner_just_key)->hashState,state->message) == (&state->inner)->hashState)
        _(ghost \state s = \now())
        int res = s2n_hash_update(&state->inner, in, size);
        _(assert state->alg ==> (&state->inner)->hashState == concatenate(\at(s,(&state->inner)->hashState),make_num((uint8_t *)in,size)))
        _(ghost state->message = deconcatenate((&state->inner_just_key)->hashState.len,(&state->inner)->hashState))
        _(wrap state) 
        return res; 
    }
}

static int s2n_sslv3_mac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires is_sslv3(state->alg))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures \result <= 0)
    _(ensures !\result ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))
    _(ensures \unchanged(state->alg))
    _(ensures !\result ==> !state->valid)
    _(ensures \unchanged(state->key))
    _(ensures \unchanged(state->message))
{
    _(unwrap state)
    _(assert \wrapped_with_deep_domain(&state->inner))
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==0x5c){
        state->xor_pad[i] = 0x5c;
    }
    _(ghost state->xorpad.val = (\lambda \natural i; i<state->block_size? state->xor_pad[i] : (uint8_t)0x0))
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(ghost \state s= \now())
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->valid = (&state->inner)->valid)
    _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0x0))
    _(assert state->digestpad == hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg)))
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    //memcpy/*_check*//*(&state->inner, &state->outer, sizeof(state->inner));
    _(wrap state)
    _(assert \wrapped_with_deep_domain(state))
    _(ghost hmac_state_destroy(state);)
    state->inner = state->outer; //USER ADDED INSTEAD OF MEMCPY
    _(ghost state->valid = (&state->inner)->valid)
    _(ghost wrap_hash_states(state))
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->inner, state->digest_pad, state->digest_size));
    _(assert (&state->inner)->hashState == concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg))))
    {
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res= s2n_hash_digest(&state->inner, outt, size);
        _(ghost state->valid = (&state->inner)->valid)
        _(wrap state)
        return res;
    }
}

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures \unchanged(state->alg))
    _(ensures !\result && is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))
    _(ensures !\result && state->key.len>state->block_size ==> !is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)),hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures !\result && state->key.len<=state->block_size ==> !is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(state->key,state->block_size),repeat(0x5c,state->block_size)),hashVal(concatenate(xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures \unchanged(state->key))
    _(ensures \unchanged(state->message))
    _(ensures !\result ==> !state->valid)
    _(ensures \result <= 0)
;

int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    if (state->alg == S2N_HMAC_SSLv3_SHA1 || state->alg == S2N_HMAC_SSLv3_MD5) {
        return s2n_sslv3_mac_digest(state, outt, size);
    }
    _(unwrap state)
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(ghost \state s = \now())
    _(assert (&state->inner)->hashState == concatenate((&state->inner_just_key)->hashState,state->message))
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->valid = (&state->inner)->valid)
    _(ghost state->digestpad.val = (\lambda \natural i; i<state->digest_size? state->digest_pad[i] : (uint8_t)0x0))
    _(assert state->digestpad == hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg)))
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_reset(&state->outer));
    _(assert (&state->outer)->hashState == repeat(0x0,0))
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));
    _(assert \wrapped_with_deep_domain(&state->inner))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->digest_pad, state->digest_size));
    _(assert (&state->outer)->hashState == concatenate(state->xorpad,state->digestpad))  
    { 
        _(assert \wrapped_with_deep_domain(&state->inner))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res = s2n_hash_digest(&state->outer,outt, size);
        _(wrap state)
        return res; 
    }
}

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires !is_sslv3(state->alg))
    _(writes state, \array_range(_(uint8_t *)outt,size))
    _(ensures !\result && !is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size)==hashVal(concatenate(state->xorpad,state->digestpad),hmac_to_hash(state->alg)))  
    _(ensures !\result && is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == hashVal(concatenate(\old((&state->outer)->hashState),state->digestpad),hmac_to_hash(state->alg)))
    _(ensures \result <= 0)   
    _(ensures !state->valid)
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
    _(assert state->alg && !is_sslv3(state->alg) ==> (&state->outer)->hashState == repeat(0x0,0))

    _(unwrap state)
    _(assert state->alg && !is_sslv3(state->alg) ==> (&state->outer)->hashState == repeat(0x0,0))
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

/*extern int s2n_constant_time_equals(const uint8_t *a, const uint8_t *b, uint32_t len)
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
}*/

extern int s2n_hmac_reset(struct s2n_hmac_state *state)
    _(maintains \wrapped(state))
    _(writes state)
    _(ensures state->message == repeat(0x0,0))
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(state->key))
    _(ensures \result <= 0)
    _(ensures state->valid)
    _(decreases 0) 
;

int s2n_hmac_reset(struct s2n_hmac_state *state)
{
    _(unwrap state)
    state->currently_in_hash_block = 0;
    //memcpy_check(&state->inner, &state->inner_just_key, sizeof(state->inner));
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    _(wrap state)
    _(assert \wrapped_with_deep_domain(state))
    _(ghost hmac_state_destroy(state);)
    state->inner = state->inner_just_key; //USER ADDED
    _(ghost state->valid = (&state->inner)->valid)
    _(ghost state->message = deconcatenate((&state->inner_just_key)->hashState.len,(&state->inner)->hashState))
    _(ghost wrap_hmac_state(state))
    return 0;
}

_(ghost int hmac_state_destroy(struct s2n_hmac_state *s)
    _(requires \wrapped(s) || \mutable(s))
    _(writes s)
    _(ensures s->digestpad == make_num(s->digest_pad,s->digest_size))
    _(ensures s->xorpad == make_num(s->xor_pad,s->block_size))
    _(ensures \forall size_t i; i<128 ==> \unchanged(s->xor_pad[i]))
    _(ensures \forall size_t i; i<SHA512_DIGEST_LENGTH ==> \unchanged(s->digest_pad[i]))
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
    _(ensures \unchanged((&s->inner)->hashState))
    _(ensures \unchanged((&s->outer)->hashState))
    _(ensures \unchanged(s->message))
    _(ensures \unchanged((&s->inner_just_key)->hashState))
    _(ensures \unchanged(s->valid) && \unchanged((&s->inner)->valid) && \unchanged((&s->outer)->valid) && \unchanged((&s->inner_just_key)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_MD5    ==> \union_active(&(&s->inner)->hash_ctx.md5)    && \union_active(&(&s->outer)->hash_ctx.md5)    && \union_active(&(&s->inner_just_key)->hash_ctx.md5)    && \unchanged((&(&s->inner_just_key)->hash_ctx.md5)->val)    && \unchanged((&(&s->inner)->hash_ctx.md5)->val)    && \unchanged((&(&s->outer)->hash_ctx.md5)->val)    && \unchanged((&(&s->inner_just_key)->hash_ctx.md5)->valid)    && \unchanged((&(&s->inner)->hash_ctx.md5)->valid)    && \unchanged((&(&s->outer)->hash_ctx.md5)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA1   ==> \union_active(&(&s->inner)->hash_ctx.sha1)   && \union_active(&(&s->outer)->hash_ctx.sha1)   && \union_active(&(&s->inner_just_key)->hash_ctx.sha1)   && \unchanged((&(&s->inner_just_key)->hash_ctx.sha1)->val)   && \unchanged((&(&s->inner)->hash_ctx.sha1)->val)   && \unchanged((&(&s->outer)->hash_ctx.sha1)->val)   && \unchanged((&(&s->inner_just_key)->hash_ctx.sha1)->valid)   && \unchanged((&(&s->inner)->hash_ctx.sha1)->valid)   && \unchanged((&(&s->outer)->hash_ctx.sha1)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA224 ==> \union_active(&(&s->inner)->hash_ctx.sha224) && \union_active(&(&s->outer)->hash_ctx.sha224) && \union_active(&(&s->inner_just_key)->hash_ctx.sha224) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha224)->val) && \unchanged((&(&s->inner)->hash_ctx.sha224)->val) && \unchanged((&(&s->outer)->hash_ctx.sha224)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha224)->valid) && \unchanged((&(&s->inner)->hash_ctx.sha224)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha224)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA256 ==> \union_active(&(&s->inner)->hash_ctx.sha256) && \union_active(&(&s->outer)->hash_ctx.sha256) && \union_active(&(&s->inner_just_key)->hash_ctx.sha256) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha256)->val) && \unchanged((&(&s->inner)->hash_ctx.sha256)->val) && \unchanged((&(&s->outer)->hash_ctx.sha256)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha256)->valid) && \unchanged((&(&s->inner)->hash_ctx.sha256)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha256)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA384 ==> \union_active(&(&s->inner)->hash_ctx.sha384) && \union_active(&(&s->outer)->hash_ctx.sha384) && \union_active(&(&s->inner_just_key)->hash_ctx.sha384) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha384)->val) && \unchanged((&(&s->inner)->hash_ctx.sha384)->val) && \unchanged((&(&s->outer)->hash_ctx.sha384)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha384)->valid) && \unchanged((&(&s->inner)->hash_ctx.sha384)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha384)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA512 ==> \union_active(&(&s->inner)->hash_ctx.sha512) && \union_active(&(&s->outer)->hash_ctx.sha512) && \union_active(&(&s->inner_just_key)->hash_ctx.sha512) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha512)->val) && \unchanged((&(&s->inner)->hash_ctx.sha512)->val) && \unchanged((&(&s->outer)->hash_ctx.sha512)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha512)->valid) && \unchanged((&(&s->inner)->hash_ctx.sha512)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha512)->valid))
    _(ensures \unchanged(s->key))
    _(ensures \unchanged(hashVal(s->key,hmac_to_hash(s->alg))))
    _(decreases 0)
;)

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(requires \wrapped(from))
    _(requires \extent_mutable(to))
    _(requires from != to)
    _(requires from->valid)
    _(writes \extent(to), from)
    _(ensures \wrapped(to))
    _(ensures \result <= 0)
    _(ensures hashState(&to->inner,0) == \old(hashState(&from->inner,0)))
    _(ensures to->valid)
; 

int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
{
    _(assert sizeof(struct s2n_hmac_state) ==> to != NULL)
    //memcpy_check(to, from, sizeof(struct s2n_hmac_state));
    _(assert \wrapped_with_deep_domain(from))
    _(ghost hmac_state_destroy(from);)
    *to = *from; //USED ADDED IN PLACE OF MEMCPY
    _(ghost wrap_hmac_state(to);)
    return 0;
}
/*
int testing()
{
    uint32_t size = 20;
    uint32_t size1 = 20;
    uint32_t size2 = 20;
    uint8_t *data = malloc(sizeof (uint8_t) * size);
    uint8_t *data1 = malloc(sizeof (uint8_t) * size1);
    uint8_t *data2 = malloc(sizeof (uint8_t) * size2);
    struct s2n_blob *key = malloc(sizeof(*key));
    if(key==NULL) return -1;
    //how can I make the array writable?
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
    s2n_hmac_algorithm r = S2N_HMAC_SHA1;
    _(assert \wrapped_with_deep_domain(key))
    GUARD(s2n_hmac_init(state,r,key->data,key->size)); //\wrapped(\domain_root(\embedding((uint8_t*)key->data))) fails. If I unwrap key, I get unreachable code
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> (&state->inner)->hashState== xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    GUARD(s2n_hmac_update(state,b->data,b->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> (&state->inner)->hashState==concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)),make_num(b->data,b->size)))
    GUARD(s2n_hmac_digest(state,outt->data,outt->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> make_num(outt->data,outt->size) == hashVal(concatenate(xor(num_resize(hashVal(make_num(key->data,key->size),hmac_to_hash(r)),block_size_alg(r)),repeat(0x5c,block_size_alg(r))),hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)),make_num(b->data,b->size)),hmac_to_hash(r))),hmac_to_hash(r)))
}
*/

