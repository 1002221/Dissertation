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
    _(invariant valid ==> (&inner)->valid)
    _(invariant (&inner_just_key)->valid)
    _(invariant is_sslv3(alg) ==> (&outer)->valid)
    _(ghost Num key)
    _(ghost Num message)
    _(invariant valid_num(message))
    _(invariant valid ==> concatenate((&inner_just_key)->hashState,message) == (&inner)->hashState)
    struct s2n_hash_state inner;
    struct s2n_hash_state inner_just_key;
    struct s2n_hash_state outer;
    _(ghost \bool real)
    _(invariant (&inner_just_key)->real && (&outer)->real)
    _(invariant real ==> (&inner)->real)
    _(invariant key.len <= block_size && alg && !is_sslv3(alg)  ==> 
        (&inner_just_key)->hashState == xor(num_resize(key,block_size),repeat(0x36,block_size)))
    _(invariant key.len > block_size && alg && !is_sslv3(alg)  ==> 
        (&inner_just_key)->hashState == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x36,block_size)))
    _(invariant !alg ==> (&inner_just_key)->hashState == repeat(0x0,0))
    _(invariant !is_sslv3(alg)  ==> (&outer)->hashState == repeat(0x0,0))
    _(invariant is_sslv3(alg)   ==> (&inner_just_key)->hashState == concatenate(key,repeat(0x36,block_size)))
    _(invariant is_sslv3(alg) ==> (&outer)->hashState == concatenate(key,repeat(0x5c,block_size)))
    /* key needs to be as large as the biggest block size */
    uint8_t xor_pad[128];
    _(invariant key.len>block_size && alg && !is_sslv3(alg) ==> 
        make_num(xor_pad,block_size) == xor(num_resize(hashVal(key,hmac_to_hash(alg)),block_size),repeat(0x5c,block_size)))
    _(invariant key.len>block_size && !alg && !is_sslv3(alg) ==> make_num(xor_pad,block_size) == repeat(0x5c,block_size))
    _(invariant key.len<=block_size && !is_sslv3(alg) ==> 
        make_num(xor_pad,block_size) == xor(num_resize(key,block_size),repeat(0x5c,block_size)))
    _(invariant is_sslv3(alg) ==> make_num(xor_pad,block_size) == repeat(0x5c,block_size))
    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];
    _(invariant alg>=0 && alg <= 8)
    _(invariant valid==>(&inner)->alg == hmac_to_hash(alg))
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
    if (alg>=7 && alg<=8) return 1;
    else return 0; 
})

_(def \bool is_valid_hmac(s2n_hmac_algorithm alg)
{
    if (alg>=0 && alg<=8) return 1;
    else return 0; 
})

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires is_valid_hmac(alg))
    _(writes \extent(state))
    _(ensures state->message == repeat(0x0,0))
    _(ensures \result == 0)
    _(ensures \wrapped(state))
    _(ensures state->alg == alg)
    _(ensures state->key == make_num((uint8_t *)key,klen))
    _(ensures state->valid)
    _(ensures state->real)
    _(decreases 0)
    ;
  
extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(maintains \wrapped(state))
    _(maintains state->valid)
    _(maintains state->real)
    _(requires \thread_local_array((uint8_t *)in,size))
    _(writes state)
    _(ensures state->alg ==> state->message == concatenate(\old(state->message),make_num((uint8_t *)in,size)))
    _(ensures !state->alg ==> state->message == repeat(0x0,0))
    _(ensures \unchanged(state->alg))
    _(ensures \unchanged(state->key))
    _(ensures \result == 0);

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(maintains state->real)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures \unchanged(state->alg))
    _(ensures is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == 
        hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),
        hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),state->message),
        hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))
    _(ensures state->alg && state->key.len>state->block_size && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(hashVal(state->key,
        hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)),
        hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),
        repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures state->alg && state->key.len<=state->block_size && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(state->key,state->block_size),
        repeat(0x5c,state->block_size)),hashVal(concatenate(xor(num_resize(state->key,state->block_size),
        repeat(0x36,state->block_size)),state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures !state->alg ==> make_num((uint8_t *)outt,size) == repeat(0x0,0))
    _(ensures \unchanged(state->key))
    _(ensures \unchanged(state->message))
    _(ensures !state->valid)
    _(ensures \result == 0)
;

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(maintains \wrapped(state))
    _(requires state->valid)
    _(ensures !state->valid)
    _(maintains state->real)
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(requires !is_sslv3(state->alg))
    _(writes state, \array_range(_(uint8_t *)outt,size))
    _(ensures is_sslv3(state->alg) ==> make_num((uint8_t *)outt,size) == 
        hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),
        hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),\old(state->message)),
        hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))
    _(ensures state->alg && state->key.len>state->block_size && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(hashVal(state->key,
        hmac_to_hash(state->alg)),state->block_size),repeat(0x5c,state->block_size)),
        hashVal(concatenate(xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),
        repeat(0x36,state->block_size)),\old(state->message)),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures state->alg && state->key.len<=state->block_size && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(state->key,state->block_size),
        repeat(0x5c,state->block_size)),hashVal(concatenate(xor(num_resize(state->key,state->block_size),
        repeat(0x36,state->block_size)),\old(state->message)),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(ensures !state->alg ==> make_num((uint8_t *)outt,size) == repeat(0x0,0))
    _(ensures \result == 0)   
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
    _(ensures \result == 0)
    _(ensures state->valid)
    _(ensures state->real)
    _(decreases 0) 
;

_(ghost int hmac_state_destroy(struct s2n_hmac_state *s)
    _(requires \wrapped(s) || \mutable(s))
    _(writes s)
    /*_(ensures \forall size_t i; i<128 ==> \unchanged(s->xor_pad[i]))
    _(ensures \forall size_t i; i<SHA512_DIGEST_LENGTH ==> \unchanged(s->digest_pad[i]))*/
    _(ensures /*\unchanged(make_num(s->digest_pad,s->digest_size)) && */\unchanged(make_num(s->xor_pad,s->block_size)))
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
    _(ensures \unchanged(s->real))
    _(ensures \unchanged((&s->inner_just_key)->hashState))
    _(ensures \unchanged(s->valid) && \unchanged((&s->inner)->valid) && \unchanged((&s->outer)->valid) && 
        \unchanged((&s->inner_just_key)->valid))
    _(ensures \unchanged((&s->inner)->real) && \unchanged((&s->outer)->real) && 
        \unchanged((&s->inner_just_key)->real))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_MD5    ==> \union_active(&(&s->inner)->hash_ctx.md5)    && 
        \union_active(&(&s->outer)->hash_ctx.md5)    && \union_active(&(&s->inner_just_key)->hash_ctx.md5)    
        && \unchanged((&(&s->inner_just_key)->hash_ctx.md5)->val)    && \unchanged((&(&s->inner)->hash_ctx.md5)->val)    
        && \unchanged((&(&s->outer)->hash_ctx.md5)->val)    && \unchanged((&(&s->inner_just_key)->hash_ctx.md5)->valid)    
        && \unchanged((&(&s->inner)->hash_ctx.md5)->valid)    && \unchanged((&(&s->outer)->hash_ctx.md5)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA1   ==> \union_active(&(&s->inner)->hash_ctx.sha1)   && 
        \union_active(&(&s->outer)->hash_ctx.sha1)   && \union_active(&(&s->inner_just_key)->hash_ctx.sha1)   
        && \unchanged((&(&s->inner_just_key)->hash_ctx.sha1)->val)   && \unchanged((&(&s->inner)->hash_ctx.sha1)->val)   
        && \unchanged((&(&s->outer)->hash_ctx.sha1)->val)   && \unchanged((&(&s->inner_just_key)->hash_ctx.sha1)->valid)   
        && \unchanged((&(&s->inner)->hash_ctx.sha1)->valid)   && \unchanged((&(&s->outer)->hash_ctx.sha1)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA224 ==> \union_active(&(&s->inner)->hash_ctx.sha224) && 
        \union_active(&(&s->outer)->hash_ctx.sha224) && \union_active(&(&s->inner_just_key)->hash_ctx.sha224) && 
        \unchanged((&(&s->inner_just_key)->hash_ctx.sha224)->val) && \unchanged((&(&s->inner)->hash_ctx.sha224)->val) && 
        \unchanged((&(&s->outer)->hash_ctx.sha224)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha224)->valid) && 
        \unchanged((&(&s->inner)->hash_ctx.sha224)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha224)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA256 ==> \union_active(&(&s->inner)->hash_ctx.sha256) && 
        \union_active(&(&s->outer)->hash_ctx.sha256) && \union_active(&(&s->inner_just_key)->hash_ctx.sha256) && 
        \unchanged((&(&s->inner_just_key)->hash_ctx.sha256)->val) && \unchanged((&(&s->inner)->hash_ctx.sha256)->val) && 
        \unchanged((&(&s->outer)->hash_ctx.sha256)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha256)->valid) && 
        \unchanged((&(&s->inner)->hash_ctx.sha256)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha256)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA384 ==> \union_active(&(&s->inner)->hash_ctx.sha384) && 
        \union_active(&(&s->outer)->hash_ctx.sha384) && \union_active(&(&s->inner_just_key)->hash_ctx.sha384) && 
        \unchanged((&(&s->inner_just_key)->hash_ctx.sha384)->val) && \unchanged((&(&s->inner)->hash_ctx.sha384)->val) && 
        \unchanged((&(&s->outer)->hash_ctx.sha384)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha384)->valid) && 
        \unchanged((&(&s->inner)->hash_ctx.sha384)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha384)->valid))
    _(ensures hmac_to_hash(s->alg) == S2N_HASH_SHA512 ==> \union_active(&(&s->inner)->hash_ctx.sha512) && 
        \union_active(&(&s->outer)->hash_ctx.sha512) && \union_active(&(&s->inner_just_key)->hash_ctx.sha512) && 
        \unchanged((&(&s->inner_just_key)->hash_ctx.sha512)->val) && \unchanged((&(&s->inner)->hash_ctx.sha512)->val) && 
        \unchanged((&(&s->outer)->hash_ctx.sha512)->val) && \unchanged((&(&s->inner_just_key)->hash_ctx.sha512)->valid) && 
        \unchanged((&(&s->inner)->hash_ctx.sha512)->valid) && \unchanged((&(&s->outer)->hash_ctx.sha512)->valid))
    _(ensures \unchanged(s->key))
    _(ensures \unchanged(hashVal(s->key,hmac_to_hash(s->alg))))
    _(decreases 0)
;)

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(requires \wrapped(from))
    _(requires \extent_mutable(to))
    _(requires from != to)
    _(requires from->valid)
    _(requires from->real)
    _(writes \extent(to), from)
    _(ensures \wrapped(to))
    _(ensures \result == 0)
    _(ensures hashState(&to->inner,0) == \old(hashState(&from->inner,0)))
    _(ensures to->valid)
    _(ensures to->real)
; 



