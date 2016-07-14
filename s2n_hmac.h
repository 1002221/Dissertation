
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
#include <string.h>
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

    /* For storing the inner digest */
    uint8_t digest_pad[SHA512_DIGEST_LENGTH];

    _(invariant alg == S2N_HMAC_SHA1)
    _(invariant \mine(&inner) && \mine(&outer) && \mine(&inner_just_key) /*&& \mine((uint8_t[SHA512_DIGEST_LENGTH])digest_pad)*/)
};

extern int s2n_hmac_digest_size(s2n_hmac_algorithm alg)
    _(requires alg >= 0 && alg <= 8)
    _(requires alg == S2N_HMAC_SHA1)
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

extern int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires \extent_mutable(state))
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)state->digest_pad, state->digest_size))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires \domain_root(\embedding(state->digest_pad)) != &state->outer)
    _(requires alg == S2N_HMAC_SHA1)
    _(writes \extent(state))
    _(ensures !\result==> \wrapped(state))
;

int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
{
    s2n_hash_algorithm hash_alg = S2N_HASH_NONE;
    //state->currently_in_hash_block = 0;
    //state->digest_size = 0;
    //state->block_size = 64;
    //state->hash_block_size = 64;
    
    
    /*switch (alg) {
    case S2N_HMAC_NONE:
        break;
    case S2N_HMAC_SSLv3_MD5:
        state->block_size = 48;
         //Fall through ... 
    case S2N_HMAC_MD5:
        hash_alg = S2N_HASH_MD5;
        state->digest_size = MD5_DIGEST_LENGTH;
        break;
    case S2N_HMAC_SSLv3_SHA1:
        state->block_size = 40;
        // Fall through ... */
    /*case S2N_HMAC_SHA1:*/
        hash_alg = S2N_HASH_SHA1;
        state->block_size = 40; //user-added because VCC doesn't allow for fall through (?)
        state->digest_size = SHA_DIGEST_LENGTH;
        /*break;*/
    /*case S2N_HMAC_SHA224:
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
        return -1;
    }*/
    _(assert sizeof(state->xor_pad) >= state->block_size)
    //gte_check(sizeof(state->xor_pad), state->block_size);
    _(assert sizeof(state->digest_pad) >= state->digest_size)
    //gte_check(sizeof(state->digest_pad), state->digest_size);
    state->alg = alg;
    
    /*if (alg == S2N_HMAC_SSLv3_SHA1 || alg == S2N_HMAC_SSLv3_MD5) {
        //return s2n_sslv3_mac_init(state, alg, key, klen);
        ;
    }*/

    /*GUARD(*/s2n_hash_init(&state->inner_just_key, hash_alg)/*)*/;
    /*GUARD(*/s2n_hash_init(&state->outer, hash_alg)/*)*/;
    
    uint32_t copied = klen;
    
    if (klen > state->block_size) {
        GUARD(s2n_hash_update(&state->outer, key, klen));
        GUARD(s2n_hash_digest(&state->outer, state->digest_pad, state->digest_size)); 

        memcpy/*_check*/(state->xor_pad, state->digest_pad, state->digest_size);
        copied = state->digest_size;
    } else {
        memcpy/*_check*/(state->xor_pad, key, klen);
    }
    for (int i = 0; i < (int) copied; i++) 
        _(writes \array_range(state->xor_pad,copied)){
        state->xor_pad[i] ^= 0x36;
    }
    state->xor_pad[0] = 0x36;
    _(assert state->block_size <= 128)
    _(assert copied <= state->block_size)
    _(assert 0<= copied)
    for (uint32_t i = copied; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size)){
        state->xor_pad[i] = 0x36;
    }
    /*GUARD(*/s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size)/*)*/;
    
    // 0x36 xor 0x5c == 0x6a 
    for (int i = 0; i < state->block_size; i++) 
    _(writes \array_range(state->xor_pad,128)){
        state->xor_pad[i] ^= 0x6a;
    }
    _(union_reinterpret &(&state->inner)->hash_ctx.sha1)
    (&state->inner)->alg = S2N_HASH_SHA1;
    _(wrap &(&state->inner)->hash_ctx.sha1)
    _(wrap &(&state->inner)->hash_ctx)
    _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx.sha1, &(&state->inner)->hash_ctx})
    _(wrap &state->inner)
    _(ghost state->\owns = {&state->inner, &state->outer, &state->inner_just_key})
    _(wrap state)
    return s2n_hmac_reset(state);
}


extern int s2n_hmac_update(struct s2n_hmac_state *state, const void *in, uint32_t size)
    _(requires \wrapped(state))
    _(requires \thread_local_array((uint8_t *)in,size))
    _(writes state)
    _(requires state->currently_in_hash_block + (4294949760 + size) % state->hash_block_size <= _UI32_MAX - SYSTEM_PAGE_SIZE())
    _(requires state->hash_block_size != 0)
    _(requires state->block_size != 0)
    _(ensures !\result ==> \wrapped(state))
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

extern int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires (&state->inner)->alg == S2N_HASH_SHA1)
    _(requires (&state->outer)->alg == S2N_HASH_SHA1)
    _(requires (&state->outer)->alg == S2N_HASH_SHA1 ==> size == 20)
    _(requires (&state->inner)->alg == S2N_HASH_SHA1 ==> state->digest_size == 20)
    _(requires \thread_local_array((uint8_t *)outt, size))
    _(requires \thread_local_array((uint8_t *)state->digest_pad, state->digest_size))
    _(requires \thread_local_array((uint8_t *)state->xor_pad, state->block_size))
    _(requires !((uint8_t *) state->digest_pad \in \domain(&state->inner)))
    _(requires !((uint8_t *) outt \in \domain(&state->outer)))
    _(requires !((uint8_t *) state->xor_pad \in \domain(&state->outer)))
    _(writes state, (uint8_t *)outt)
    _(ensures !\result ==> \wrapped(state))
    _(ensures \unchanged(state->hash_block_size))
    _(ensures \result <= 0);

int s2n_hmac_digest(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    /*if (state->alg == S2N_HMAC_SSLv3_SHA1 || state->alg == S2N_HMAC_SSLv3_MD5) {
        //return s2n_sslv3_mac_digest(state, out, size);
    }*/
    _(unwrap state)
    /*GUARD(*/s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size)/*)*/;
    /*GUARD(*/s2n_hash_reset(&state->outer)/*)*/;
    /*GUARD(*/s2n_hash_update(&state->outer, state->xor_pad, state->block_size)/*)*/;
    /*GUARD(*/s2n_hash_update(&state->outer, state->digest_pad, state->digest_size)/*)*/;

    { 
        int res = s2n_hash_digest(&state->outer, (uint8_t *)outt, size);
        _(wrap state) 
        return res; 
    }
}

extern int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
    _(requires \wrapped(state))
    _(requires (&state->inner)->alg == S2N_HASH_SHA1)
    _(requires (&state->outer)->alg == S2N_HASH_SHA1)
    _(requires (&state->outer)->alg == S2N_HASH_SHA1 ==> size == 20)
    _(requires (&state->inner)->alg == S2N_HASH_SHA1 ==> state->digest_size == 20)
    _(requires \thread_local_array((uint8_t *)outt, size))
    _(requires \thread_local_array((uint8_t *)state->digest_pad, state->digest_size))
    _(requires \thread_local_array((uint8_t *)state->xor_pad, state->block_size))
    _(requires \thread_local_array((uint8_t *)state->xor_pad, state->hash_block_size))
    _(requires !((uint8_t *) state->digest_pad \in \domain(&state->inner)))
    _(requires !((uint8_t *) outt \in \domain(&state->outer)))
    _(requires !((uint8_t *) state->xor_pad \in \domain(&state->outer)))
    _(writes state, (uint8_t *)outt)
    _(requires (&state->outer)->alg == S2N_HASH_SHA1 ==> size == SHA_DIGEST_LENGTH)
    _(requires state->hash_block_size > 9)
    _(ensures !\result ==> \wrapped(state))
    _(ensures \result <= 0)    
    ;

int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    GUARD(s2n_hmac_digest(state, (uint8_t *)outt, size));

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

extern int s2n_hmac_digest_verify(const void *a, const void *b, uint32_t len);



extern int s2n_hmac_reset(struct s2n_hmac_state *state)
    _(maintains \wrapped(state))
    _(writes state)
    _(ensures \result == 0)
;

int s2n_hmac_reset(struct s2n_hmac_state *state)
{
    _(unwrap state)
    state->currently_in_hash_block = 0;
    _(unwrap (&state->inner))
    memcpy/*_check*/(&state->inner, &state->inner_just_key, sizeof(state->inner));
    _(wrap (&state->inner))
    _(wrap state)
    return 0;
}

extern int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
    _(requires \wrapped(from))
    _(requires \extent_mutable(to))
    _(requires from != to)
    _(writes \extent(to))
    _(ensures \wrapped(from) && \wrapped(to))
    _(ensures \result <= 0)
; 

int s2n_hmac_copy(struct s2n_hmac_state *to, struct s2n_hmac_state *from)
{
    memcpy/*_check*/(to, from, sizeof(struct s2n_hmac_state));
    _(union_reinterpret &(&to->inner_just_key)->hash_ctx.sha1)
    (&to->inner_just_key)->alg = S2N_HASH_SHA1;
    _(wrap &(&to->inner_just_key)->hash_ctx)
    _(wrap &(&to->inner_just_key)->hash_ctx.sha1)
    _(ghost (&to->inner_just_key)->\owns = {&(&to->inner_just_key)->hash_ctx.sha1, &(&to->inner_just_key)->hash_ctx})
    _(wrap (&to->inner_just_key))
    _(union_reinterpret &(&to->outer)->hash_ctx.sha1)
    (&to->outer)->alg = S2N_HASH_SHA1;
    _(wrap &(&to->outer)->hash_ctx)
    _(wrap &(&to->outer)->hash_ctx.sha1)
    _(ghost (&to->outer)->\owns = {&(&to->outer)->hash_ctx.sha1, &(&to->outer)->hash_ctx})
    _(wrap (&to->outer))
    _(union_reinterpret &(&to->inner)->hash_ctx.sha1)
    (&to->inner)->alg = S2N_HASH_SHA1;
    _(wrap &(&to->inner)->hash_ctx)
    _(wrap &(&to->inner)->hash_ctx.sha1)
    _(ghost (&to->inner)->\owns = {&(&to->inner)->hash_ctx.sha1, &(&to->inner)->hash_ctx})
    _(wrap (&to->inner))
    to->alg = S2N_HMAC_SHA1;
    _(wrap to)
    return 0;
}
