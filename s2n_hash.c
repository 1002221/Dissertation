#include "s2n_hash.h"

#define mycomm(in) _(wrap &state->hash_ctx)\
    _(ghost state->hashState = (&state->hash_ctx. ## in ## )->val)\
        _(ghost state->\owns = {&state->hash_ctx. ## in ## , &state->hash_ctx})\
        _(ghost state->valid = (&state->hash_ctx. ## in ## )->valid)

int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
{
    int r;
    switch (alg) {
    case S2N_HASH_NONE:
        r = 1;
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = repeat(0x0,0))
        _(ghost state->\owns = {&state->hash_ctx})
        _(ghost state->valid = 1)
    break;
    case S2N_HASH_MD5:
        _(union_reinterpret &state->hash_ctx.md5)
        r = MD5_Init(&state->hash_ctx.md5);
        mycomm(md5)
    break;
    case S2N_HASH_SHA1:
        _(union_reinterpret &state->hash_ctx.sha1)
        r = SHA1_Init(&state->hash_ctx.sha1);
        mycomm(sha1)
    break;
    case S2N_HASH_SHA224:
        _(union_reinterpret &state->hash_ctx.sha224)
        r = SHA224_Init(&state->hash_ctx.sha224);
        mycomm(sha224)
    break;
    case S2N_HASH_SHA256:
        _(union_reinterpret &state->hash_ctx.sha256)
        r = SHA256_Init(&state->hash_ctx.sha256);
        mycomm(sha256)
    break;
    case S2N_HASH_SHA384:
        _(union_reinterpret &state->hash_ctx.sha384)
        r = SHA384_Init(&state->hash_ctx.sha384);
        mycomm(sha384)
    break;
    case S2N_HASH_SHA512:
        _(union_reinterpret &state->hash_ctx.sha512)
        r = SHA512_Init(&state->hash_ctx.sha512);
        mycomm(sha512)
    break;
    case S2N_HASH_MD5_SHA1:
        _(union_reinterpret &state->hash_ctx.md5_sha1)
        r = SHA1_Init(&state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Init(&state->hash_ctx.md5_sha1.md5);
        _(wrap &state->hash_ctx.md5_sha1)
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.md5_sha1.sha1)->val)
        _(ghost state->\owns = {&state->hash_ctx.md5_sha1, &state->hash_ctx.md5_sha1.sha1, 
            &state->hash_ctx.md5_sha1.md5, &state->hash_ctx})
        _(ghost state->valid = (&state->hash_ctx.md5_sha1.md5)->valid)
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INvalid_ALGORITHM);
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
#undef mycomm

int s2n_hash_update(struct s2n_hash_state *state, const void *data, uint32_t size)
{
    //_(assume state->alg != 7)
    int r;
    _(assert \wrapped_with_deep_domain(state))
    _(ghost \state o = \now())
    _(unwrap state)
    _(assert make_num((uint8_t*)data,size) == \at(o,make_num((uint8_t*)data,size)))
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        _(ghost \state t = \now())
        _(ghost state->hashState = concatenate(\at(t,state->hashState), make_num((uint8_t*)data,size)))
        break; 
    case S2N_HASH_MD5:
    _(assert make_num((uint8_t*)data,size) == \at(o,make_num((uint8_t*)data,size)))

        r = MD5_Update(&state->hash_ctx.md5, data, size);
    _(assert make_num((uint8_t*)data,size) == \at(o,make_num((uint8_t*)data,size)))

        _(ghost state->hashState = (&state->hash_ctx.md5)->val)
        break;
    case S2N_HASH_SHA1:
        r = SHA1_Update(&state->hash_ctx.sha1, data, size);
        _(ghost state->hashState = (&state->hash_ctx.sha1)->val)
        break;
    case S2N_HASH_SHA224:
        r = SHA224_Update(&state->hash_ctx.sha224, data, size);
        _(ghost state->hashState = (&state->hash_ctx.sha224)->val)
        break;
    case S2N_HASH_SHA256:
        r = SHA256_Update(&state->hash_ctx.sha256, data, size);
        _(ghost state->hashState = (&state->hash_ctx.sha256)->val)
        break;
    case S2N_HASH_SHA384:
        r = SHA384_Update(&state->hash_ctx.sha384, data, size);
        _(ghost state->hashState = (&state->hash_ctx.sha384)->val)
        break;
    case S2N_HASH_SHA512:
        r = SHA512_Update(&state->hash_ctx.sha512, data, size);
        _(ghost state->hashState = (&state->hash_ctx.sha512)->val)
        break;
    case S2N_HASH_MD5_SHA1:
        r = SHA1_Update(&state->hash_ctx.md5_sha1.sha1, data, size);
        r = MD5_Update(&state->hash_ctx.md5_sha1.md5, data, size);
        _(ghost state->hashState = (&state->hash_ctx.md5_sha1.sha1)->val)
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INvalid_ALGORITHM);
        _(assert 0)
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        _(assert 0)
    }
    _(wrap state)
    return 0;
}

#define mycomm(in) _(ghost {state->hashState = (&state->hash_ctx.md5)->val;\
    state->valid = (&state->hash_ctx.md5)->valid;})

int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
{
    int r;
    _(unwrap state)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        _(unwrap &state->hash_ctx)
        r = MD5_Final(outt, &state->hash_ctx.md5);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA1:
        _(unwrap &state->hash_ctx)
        r = SHA1_Final(outt, &state->hash_ctx.sha1);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA224:
        _(unwrap &state->hash_ctx)
        r = SHA224_Final(outt, &state->hash_ctx.sha224);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA256:
        _(unwrap &state->hash_ctx)
        r = SHA256_Final(outt, &state->hash_ctx.sha256);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA384:
        _(unwrap &state->hash_ctx)
        r = SHA384_Final(outt, &state->hash_ctx.sha384);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_SHA512:
        _(unwrap &state->hash_ctx)
        r = SHA512_Final(outt, &state->hash_ctx.sha512);
        _(wrap &state->hash_ctx)
        break;
    case S2N_HASH_MD5_SHA1:
        r = SHA1_Final(((uint8_t *) outt) + MD5_DIGEST_LENGTH, &state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Final(outt, &state->hash_ctx.md5_sha1.md5);
        break;
    default:
        _(assert 0)
    }

    if (r == 0) {
        _(assert 0)
    }
    _(ghost state->valid = 0)
    _(ghost state->hashState = repeat(0x0, 0))
    _(wrap state)
    return 0;
}

int s2n_hash_reset(struct s2n_hash_state *state)
{
    _(ghost hash_state_destroy(state))
    return s2n_hash_init(state, state->alg);
}

int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
{
    _(ghost hash_state_destroy(from))
    *to = *from; //USER ADDED IN PLACE OF MEMCPY
    //memcpy_check(to, from, sizeof(struct s2n_hash_state));
    _(ghost wrap_hash_state((to)))
    _(ghost wrap_hash_state((from)))
    return 0;
}
