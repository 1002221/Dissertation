#include "s2n_hmac.h"

static int s2n_sslv3_mac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
    _(requires is_sslv3(alg))
    _(requires state->alg == alg)
    _(requires state->block_size == block_size_alg(alg) && state->digest_size == digest_size_alg(alg))
    _(requires \wrapped(\domain_root(\embedding((uint8_t *)key))))
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires state->hash_block_size == hash_block_size_alg(alg))
    _(requires state->key == make_num((uint8_t *)key,klen))
    _(writes \extent(state))
    _(ensures \unchanged(state->alg))
    _(ensures !\result ==> \wrapped(state))
    _(ensures !\result ==> state->message == repeat(0x0,0))
    _(ensures \result <= 0)
    _(ensures \unchanged(state->key))
    _(ensures state->valid)
    _(ensures state->real)
    _(decreases 0)
{
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

    _(ghost state->xorpad = make_num(state->xor_pad,state->block_size))
    
    _(requires hash_alg == hmac_to_hash(alg))
    _(writes \extent(&state->inner_just_key), \extent(&state->inner))
    _(ensures \wrapped(&state->inner_just_key) && \wrapped(&state->inner))
    _(ensures (&state->inner_just_key)->alg == hmac_to_hash(alg))
    _(ensures (&state->inner_just_key)->valid)
    _(ensures (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(ensures (&state->inner_just_key)->real)
    {
        s2n_hash_init(&state->inner_just_key, hash_alg);
        _(ghost (&state->inner)->real = 0)
        _(wrap &(&state->inner)->hash_ctx) 
        _(ghost (&state->inner)->\owns = {&(&state->inner)->hash_ctx}) 
        _(wrap (&state->inner))
    }
    GUARD(s2n_hash_update(&state->inner_just_key, key, klen));
    GUARD(s2n_hash_update(&state->inner_just_key, state->xor_pad, state->block_size));
    _(assert (&state->inner_just_key)->hashState == concatenate(state->key,state->xorpad))
    for (int i = 0; i < state->block_size; i++) 
        _(writes \array_range(state->xor_pad,state->block_size))
        _(invariant \forall int j; j>=0 && j<i ==> state->xor_pad[j]==0x5c){
        state->xor_pad[i] = 0x5c;
    }
    _(ghost state->xorpad = make_num(state->xor_pad,state->block_size))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    
    _(requires hash_alg == hmac_to_hash(alg))
    _(writes \extent(&state->outer))
    _(ensures \wrapped(&state->outer))
    _(ensures (&state->outer)->valid)
    _(ensures (&state->outer)->real)
    _(ensures (&state->outer)->hashState == repeat(0x0,0))
    _(ensures (&state->outer)->alg == hash_alg)
    {
        s2n_hash_init(&state->outer, hash_alg);
    }
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, key, klen));
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->outer, state->xor_pad, state->block_size));
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(ghost state->valid = 0)
    _(ghost state->real = 0)
    _(ghost state->message = repeat(0x0,0))
    _(ghost state->digestpad = make_num(state->digest_pad,state->digest_size))
    _(wrap state)
    return s2n_hmac_reset(state);
}

int s2n_hmac_init(struct s2n_hmac_state *state, s2n_hmac_algorithm alg, const void *key, uint32_t klen)
{
    _(ghost xor_ass()) //Used to establish that the XOR operation is associative
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
        memcpy(state->xor_pad, state->digest_pad, state->digest_size); //USER-ADDED
        //memcpy_check(state->xor_pad, state->digest_pad, state->digest_size);
        copied = state->digest_size;
    } else {
        memcpy(state->xor_pad, key, klen); //USER-ADDED
        //memcpy_check(state->xor_pad, key, klen);
    }
    
    _(assert state->alg && klen>state->block_size ==> 
            make_num(state->xor_pad,copied) == hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)))
    _(assert !state->alg && klen>state->block_size ==> make_num(state->xor_pad,copied) == repeat(0x0,0))
    _(assert klen<=state->block_size ==> make_num(state->xor_pad,copied) == make_num((uint8_t *)key,klen))

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
    
    _(assert make_num(state->xor_pad,block_size_alg(alg)) == 
        xor(num_resize(\at(t,make_num(state->xor_pad,copied)),block_size_alg(alg)),repeat((uint8_t)(0x36^0x6a),block_size_alg(alg))))
    _(assert make_num(state->xor_pad,block_size_alg(alg)) == 
        xor(num_resize(\at(t,make_num(state->xor_pad,copied)),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    
    _(assert make_num((uint8_t *)key,klen) == \at(t,make_num((uint8_t *)key,klen)))
    _(assert alg && klen>block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == 
        xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    _(assert !alg && klen>block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == 
        repeat(0x5c,block_size_alg(alg)))
    _(assert klen<=block_size_alg(alg) ==> make_num(state->xor_pad,block_size_alg(alg)) == 
        xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x5c,block_size_alg(alg))))
    _(assert alg && klen>block_size_alg(alg) ==> (&state->inner_just_key)->hashState == 
        xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(state->alg)),block_size_alg(alg)),
        repeat(0x36,block_size_alg(alg))))
    _(assert !alg ==> (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(assert alg && klen<=block_size_alg(alg) ==> (&state->inner_just_key)->hashState == 
        xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    
    _(ghost state->key = make_num((uint8_t *)key,klen))
    _(ghost state->xorpad = make_num(state->xor_pad,block_size_alg(alg)))
    _(ghost state->digestpad = make_num(state->digest_pad,digest_size_alg(alg)))

   /* _(requires \wrapped(\domain_root(\embedding((uint8_t *)key)))) 
    _(requires \thread_local_array((uint8_t *)key,klen))
    _(requires !((uint8_t*)key \in \domain(&state->inner)) && !((uint8_t*)key \in \domain(&state->inner_just_key)))
    _(ensures (&state->inner)->alg == hmac_to_hash(alg))
    _(maintains (&state->inner_just_key)->alg == hmac_to_hash(alg))
    _(maintains \wrapped(&state->inner_just_key) && \wrapped(&state->inner))
    _(maintains (&state->inner_just_key)->valid && (&state->inner_just_key)->real)
    _(ensures (&state->inner)->valid && (&state->inner)->real)
    _(maintains alg && klen>block_size_alg(alg) ==> (&state->inner_just_key)->hashState == 
        xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(maintains !alg ==> (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(maintains alg && klen<=block_size_alg(alg) ==> (&state->inner_just_key)->hashState == 
        xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(ensures alg && klen>block_size_alg(alg) ==> (&state->inner)->hashState == 
        xor(num_resize(hashVal(make_num((uint8_t *)key,klen),hmac_to_hash(alg)),block_size_alg(alg)),repeat(0x36,block_size_alg(alg))))
    _(ensures !alg ==> (&state->inner)->hashState == repeat(0x0,0))
    _(ensures alg && klen<=block_size_alg(alg) ==> (&state->inner)->hashState == 
        xor(num_resize(make_num((uint8_t *)key,klen),block_size_alg(alg)),repeat(0x36,block_size_alg(alg)))) 
    _(writes &state->inner_just_key,&state->inner)
    {
        _(ghost \state t = \now())
        _(ghost hash_state_destroy(&state->inner_just_key);)
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
        _(ghost hash_state_destroy(&state->inner))
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
NOTE: IN THE ORIGINAL CODE, THE FUNCTION RETURNS S2N_HMAC_RESET. AS ALL THAT FUNCTION DOES IS COPY S2N_HMAC_INNER_JUST_KEY
TO S2N_HMAC_INNER, WE HAVE COPIED THAT COMMAND AT THE END OF THIS FUNCTION TO AVOID THE EXTREMELY LENGTHY PRECONDITIONS
THAT WOULD HAVE RESULTED.
        state->inner = state->inner_just_key;
        _(assume make_num((uint8_t*)key,klen) == \at(t,make_num((uint8_t*)key,klen)))
        _(ghost wrap_hash_state((&state->inner)))
        _(ghost wrap_hash_state((&state->inner_just_key)))
        _(wrap (&state->inner))
        _(wrap (&state->inner_just_key))
    }*/
        
    _(ghost state->message = repeat(0x0,0))
    _(ghost state->valid = 0)
    _(ghost state->real = 0)
    _(wrap state)
    return s2n_hmac_reset(state);
    //return 0;
}

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
    _(maintains state->real)
    _(requires is_sslv3(state->alg))
    _(requires size == alg_digest_size(hmac_to_hash(state->alg)))
    _(writes state, \array_range(_(uint8_t *)outt, size)) 
    _(ensures \result <= 0)
    _(ensures !\result ==> make_num((uint8_t *)outt,size) == 
        hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),
        hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),state->message),
        hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))
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
    _(ghost state->xorpad = make_num(state->xor_pad,state->block_size))
    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    _(ghost \state s= \now())
    GUARD(s2n_hash_digest(&state->inner, state->digest_pad, state->digest_size));
    _(ghost state->valid = (&state->inner)->valid)
    _(ghost state->digestpad = make_num(state->digest_pad, state->digest_size))
    _(assert state->digestpad == hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg)))
    _(assert sizeof(state->inner) ==> &state->inner != NULL)
    //memcpy/*_check*//*(&state->inner, &state->outer, sizeof(state->inner));

    _(maintains \mutable(state))
    _(maintains \wrapped(&state->inner) && \wrapped(&state->outer))
    _(maintains (&state->outer)->valid)
    _(maintains (&state->outer)->real)
    _(maintains (&state->outer)->alg == hmac_to_hash(state->alg))
    _(ensures (&state->inner)->alg == (&state->outer)->alg)
    _(maintains (&state->outer)->hashState == concatenate(state->key,repeat(0x5c,state->block_size)))
    _(maintains !state->alg ==> (&state->outer)->hashState == repeat(0x0,0))
    _(maintains valid_num((&state->outer)->hashState)) //MARKED AS UNREACHABLE
    _(writes &state->outer,&state->inner)
    _(ensures (&state->inner)->hashState == (&state->outer)->hashState)
    _(ensures (&state->inner)->valid == (&state->outer)->valid)
    _(ensures (&state->inner)->real == (&state->outer)->real)
    {
        _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(ghost hash_state_destroy(&state->outer);)
        _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
        _(ghost hash_state_destroy(&state->inner))
        state->inner = state->outer;
        _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
        _(ghost wrap_hash_state((&state->inner)))
        _(ghost wrap_hash_state((&state->outer)))
        _(wrap (&state->inner))
        _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
        _(wrap (&state->outer))
        _(assert (&state->outer)->alg == hmac_to_hash(state->alg))
    }

    _(assert \wrapped_with_deep_domain(&state->outer))
    _(assert \wrapped_with_deep_domain(&state->inner_just_key))
    GUARD(s2n_hash_update(&state->inner, state->digest_pad, state->digest_size));
    _(assert (&state->inner)->hashState == 
        concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),
        hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg))))
    {
        _(assert \wrapped_with_deep_domain(&state->outer))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res= s2n_hash_digest(&state->inner, outt, size);
        _(ghost state->valid = (&state->inner)->valid)
        _(wrap state)
        return res;
    }
}

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
    _(ghost state->digestpad = make_num(state->digest_pad,state->digest_size))
    _(assert state->alg ==> state->digestpad == 
        hashVal(concatenate((&state->inner_just_key)->hashState,state->message),hmac_to_hash(state->alg)))
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
    _(assert state->alg ==> (&state->outer)->hashState == concatenate(state->xorpad,state->digestpad))  
    _(assert !state->alg ==> (&state->outer)->hashState == repeat(0x0,0))  
    { 
        _(assert \wrapped_with_deep_domain(&state->inner))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        int res = s2n_hash_digest(&state->outer,outt, size);
        _(wrap state)
        return res; 
    }
}

int s2n_hmac_digest_two_compression_rounds(struct s2n_hmac_state *state, void *outt, uint32_t size)
{
    _(assert state->hash_block_size >=9)
    
    GUARD(s2n_hmac_digest(state, outt, size));
    _(assert !state->valid)
    _(assert \inv(state))
    _(assert  state->alg && state->key.len<=state->block_size && !is_sslv3(state->alg) ==> 
        make_num((uint8_t *)outt,size) == hashVal(concatenate(xor(num_resize(state->key,state->block_size),
        repeat(0x5c,state->block_size)),
        hashVal(concatenate(xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)),
        state->message),hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))  
    _(assert !state->alg ==> make_num((uint8_t *)outt,size) == repeat(0x0,0))
    
    /* If there were 9 or more bytes of space left in the current hash block
     * then the serialized length, plus an 0x80 byte, will have fit in that block. 
     * If there were fewer than 9 then adding the length will have caused an extra 
     * compression block round. This digest function always does two compression rounds,
     * even if there is no need for the second.
     */
    _(assert \inv(state))
    if (state->currently_in_hash_block > (state->hash_block_size - 9))
    {
        return 0;
    }
    _(unwrap state)
    s2n_hash_reset(&state->inner);
    { 
        int res = s2n_hash_update(&state->inner, state->xor_pad, state->hash_block_size);
        _(wrap state)
        return res; 
    }
}

int s2n_hmac_reset(struct s2n_hmac_state *state)
{
    _(unwrap state)
    state->currently_in_hash_block = 0;
    //memcpy_check(&state->inner, &state->inner_just_key, sizeof(state->inner));
    _(assert sizeof(state->inner) ==> &state->inner != NULL)

    _(maintains \mutable(state))
    _(maintains \wrapped(&state->inner) && \wrapped(&state->inner_just_key))
    _(maintains (&state->inner_just_key)->valid)
    _(maintains (&state->inner_just_key)->real)
    _(maintains (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    _(ensures (&state->inner)->alg == (&state->inner_just_key)->alg)
    _(maintains state->key.len <= state->block_size && state->alg && !is_sslv3(state->alg)  ==> 
        (&state->inner_just_key)->hashState == xor(num_resize(state->key,state->block_size),repeat(0x36,state->block_size)))
    _(maintains state->key.len > state->block_size && state->alg && !is_sslv3(state->alg)  ==> 
        (&state->inner_just_key)->hashState == xor(num_resize(hashVal(state->key,hmac_to_hash(state->alg)),state->block_size),repeat(0x36,state->block_size)))
    _(maintains !state->alg && !is_sslv3(state->alg) ==> (&state->inner_just_key)->hashState == repeat(0x0,0))
    _(maintains is_sslv3(state->alg)   ==> (&state->inner_just_key)->hashState == concatenate(state->key,repeat(0x36,state->block_size)))
    _(maintains valid_num((&state->inner_just_key)->hashState)) //MARKED AS UNREACHABLE - IS THIS A PROBLEM?
    _(writes &state->inner_just_key,&state->inner)
    _(ensures (&state->inner)->hashState == (&state->inner_just_key)->hashState)
    _(ensures (&state->inner)->valid == (&state->inner_just_key)->valid)
    _(ensures (&state->inner)->real == (&state->inner_just_key)->real)
    {
        _(ghost \state t = \now())
        _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
        _(assert \wrapped_with_deep_domain(&state->inner_just_key))
        _(ghost hash_state_destroy(&state->inner_just_key);)
        _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
        _(ghost hash_state_destroy(&state->inner))
        state->inner = state->inner_just_key;
        _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
        _(ghost wrap_hash_state((&state->inner)))
        _(ghost wrap_hash_state((&state->inner_just_key)))
        _(wrap (&state->inner))
        _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
        _(wrap (&state->inner_just_key))
        _(assert (&state->inner_just_key)->alg == hmac_to_hash(state->alg))
    }

    _(ghost state->valid = (&state->inner)->valid)
    _(ghost state->real = (&state->inner)->real)
    _(ghost state->message = deconcatenate((&state->inner_just_key)->hashState.len,(&state->inner)->hashState))
    _(wrap state)


    return 0;
}

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
Verification of MD5state_st#adm succeeded. [40.95]
Verification of MD5state_st2#adm succeeded. [13.33]
Verification of SHAstate_st#adm succeeded. [7.19]
Verification of SHAstate_st2#adm succeeded. [7.61]
Verification of SHA224state_st#adm succeeded. [7.89]
Verification of SHA256state_st#adm succeeded. [12.30]
Verification of SHA384state_st#adm succeeded. [5.86]
Verification of SHA512state_st#adm succeeded. [7.31]
Verification of s2n_hash_state#adm succeeded. [9.25]
Verification of s2n_hmac_state#adm succeeded. [14.44]
Verification of swprintf succeeded. [1.86]
Verification of vswprintf succeeded. [1.61]
Verification of _swprintf_l succeeded. [2.06]
Verification of _vswprintf_l succeeded. [1.78]
Verification of xor succeeded. [4.28]
Verification of valid_num succeeded. [3.77]
Verification of make_num succeeded. [4.03]
Verification of repeat succeeded. [4.80]
Verification of concatenate succeeded. [5.95]
Verification of deconcatenate succeeded. [4.47]
Verification of num_resize succeeded. [12.05]
Verification of xor_ass succeeded. [1.41]
Verification of xor_combine succeeded. [1.27]
Verification of is_valid_hash succeeded. [4.66]
Verification of s2n_hash_digest_size succeeded. [3.80]
Verification of alg_digest_size succeeded. [17.53]
Verification of hashState succeeded. [17.33]
Verification of s2n_hmac_digest_size succeeded. [4.88]
Verification of block_size_alg succeeded. [9.27]
Verification of hash_block_size_alg succeeded. [5.72]
Verification of digest_size_alg succeeded. [13.66]
Verification of hmac_to_hash succeeded. [16.51]
Verification of is_sslv3 succeeded. [4.81]
Verification of is_valid_hmac succeeded. [5.23]
Verification of s2n_hmac_init succeeded. [744.80]
Verification of s2n_hmac_update succeeded. [485.14]
Verification of s2n_hmac_digest succeeded. [50.22]
Verification of s2n_hmac_digest_two_compression_rounds succeeded. [23.91]
Verification of s2n_hmac_reset succeeded. [6.39]
Verification of s2n_hmac_copy succeeded. [211.47]
Verification of s2n_sslv3_mac_init succeeded. [700.06]
Verification of s2n_sslv3_mac_digest succeeded. [39.67]
Verification of xor_ass#bv_lemma#0 succeeded. [4.44]
Verification of s2n_hmac_init#block#0 succeeded. [17.34]
Verification of s2n_hmac_reset#block#0 succeeded. [144.69]
Verification of s2n_sslv3_mac_digest#block#0 succeeded. [125.22]
Verification of s2n_sslv3_mac_init#block#0 succeeded. [1.83]
Verification of s2n_sslv3_mac_init#block#1 succeeded. [1.34]

=== Verification succeeded. ===