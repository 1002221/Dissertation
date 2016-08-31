#include "s2n_hash.h"

int s2n_hash_init(struct s2n_hash_state *state, s2n_hash_algorithm alg)
{
    int r;
    switch (alg) {
    case S2N_HASH_NONE:
        r = 1;
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = repeat(0x0,0))
        _(ghost state->\owns = {&state->hash_ctx})
        _(ghost state->usable = 1)
    break;
    case S2N_HASH_MD5:
        _(union_reinterpret &state->hash_ctx.md5)
        r = MD5_Init(&state->hash_ctx.md5);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.md5)->val)
        _(ghost state->\owns = {&state->hash_ctx.md5, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.md5)->usable)
    break;
    case S2N_HASH_SHA1:
        _(union_reinterpret &state->hash_ctx.sha1)
        r = SHA1_Init(&state->hash_ctx.sha1);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha1)->val)
        _(ghost state->\owns = {&state->hash_ctx.sha1, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.sha1)->usable)
    break;
    case S2N_HASH_SHA224:
        _(union_reinterpret &state->hash_ctx.sha224)
        r = SHA224_Init(&state->hash_ctx.sha224);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha224)->val)
        _(ghost state->\owns = {&state->hash_ctx.sha224, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.sha224)->usable)
    break;
    case S2N_HASH_SHA256:
        _(union_reinterpret &state->hash_ctx.sha256)
        r = SHA256_Init(&state->hash_ctx.sha256);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha256)->val)
        _(ghost state->\owns = {&state->hash_ctx.sha256, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.sha256)->usable)
    break;
    case S2N_HASH_SHA384:
        _(union_reinterpret &state->hash_ctx.sha384)
        r = SHA384_Init(&state->hash_ctx.sha384);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha384)->val)
        _(ghost state->\owns = {&state->hash_ctx.sha384, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.sha384)->usable)
    break;
    case S2N_HASH_SHA512:
        _(union_reinterpret &state->hash_ctx.sha512)
        r = SHA512_Init(&state->hash_ctx.sha512);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha512)->val)
        _(ghost state->\owns = {&state->hash_ctx.sha512, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.sha512)->usable)
    break;
    case S2N_HASH_MD5_SHA1:
        _(union_reinterpret &state->hash_ctx.md5_sha1)
        r = SHA1_Init2(&state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Init2(&state->hash_ctx.md5_sha1.md5);
        _(wrap &state->hash_ctx.md5_sha1)
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.md5_sha1.sha1)->val)
        _(ghost state->\owns = {&state->hash_ctx.md5_sha1, &state->hash_ctx.md5_sha1.sha1, &state->hash_ctx.md5_sha1.md5, &state->hash_ctx})
        _(ghost state->usable = (&state->hash_ctx.md5_sha1.md5)->usable)
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INusable_ALGORITHM);
        _(assert 0)
    }
    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        _(assert 0)
    }
    state->alg = alg;
    _(ghost state->real = 1)
    _(wrap state)
    return 0;
}

int s2n_hash_update(struct s2n_hash_state *state, const void *data, uint32_t size)
{
    int r;
    _(unwrap state)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        break;
    case S2N_HASH_MD5:
        r = MD5_Update(&state->hash_ctx.md5, data, size);
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
        r = SHA1_Update2(&state->hash_ctx.md5_sha1.sha1, data, size);
        r = MD5_Update2(&state->hash_ctx.md5_sha1.md5, data, size);
        _(ghost state->hashState = (&state->hash_ctx.md5_sha1.sha1)->val)
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INusable_ALGORITHM);
        _(assert 0)
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_UPDATE_FAILED);
        _(assert 0)
    }
    _(wrap state)
    return 0;
}

int s2n_hash_digest(struct s2n_hash_state *state, void *outt, uint32_t size)
{
    int r;
    _(unwrap state)
    switch (state->alg) {
    case S2N_HASH_NONE:
        r = 1;
        _(ghost state->usable = 0)
        break;
    case S2N_HASH_MD5:
        //eq_check(size, MD5_DIGEST_LENGTH);
        _(assert size == MD5_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = MD5_Final(outt, &state->hash_ctx.md5);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.md5)->val)
        _(ghost state->usable = (&state->hash_ctx.md5)->usable)
        break;
    case S2N_HASH_SHA1:
        //eq_check(size, SHA_DIGEST_LENGTH);
        _(assert size == SHA_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = SHA1_Final(outt, &state->hash_ctx.sha1);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha1)->val)
        _(ghost state->usable = (&state->hash_ctx.sha1)->usable)
        break;
    case S2N_HASH_SHA224:
        //eq_check(size, SHA224_DIGEST_LENGTH);
        _(assert size == SHA224_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = SHA224_Final(outt, &state->hash_ctx.sha224);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha224)->val)
        _(ghost state->usable = (&state->hash_ctx.sha224)->usable)
        break;
    case S2N_HASH_SHA256:
        //eq_check(size, SHA256_DIGEST_LENGTH);
        _(assert size == SHA256_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = SHA256_Final(outt, &state->hash_ctx.sha256);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha256)->val)
        _(ghost state->usable = (&state->hash_ctx.sha256)->usable)
        break;
    case S2N_HASH_SHA384:
        //eq_check(size, SHA384_DIGEST_LENGTH);
        _(assert size == SHA384_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = SHA384_Final(outt, &state->hash_ctx.sha384);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha384)->val)
        _(ghost state->usable = (&state->hash_ctx.sha384)->usable)
        break;
    case S2N_HASH_SHA512:
        //eq_check(size, SHA512_DIGEST_LENGTH);
        _(assert size == SHA512_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        _(unwrap &state->hash_ctx)
        r = SHA512_Final(outt, &state->hash_ctx.sha512);
        _(wrap &state->hash_ctx)
        _(ghost state->hashState = (&state->hash_ctx.sha512)->val)
        _(ghost state->usable = (&state->hash_ctx.sha512)->usable)
        break;
    case S2N_HASH_MD5_SHA1:
        //eq_check(size, MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH);
        _(assert size == MD5_DIGEST_LENGTH + SHA_DIGEST_LENGTH) //USER ADDED INSTEAD OF EQ_CHECK
        r = SHA1_Final2(((uint8_t *) outt) + MD5_DIGEST_LENGTH, &state->hash_ctx.md5_sha1.sha1);
        r &= MD5_Final2(outt, &state->hash_ctx.md5_sha1.md5);
        _(ghost state->hashState = (&state->hash_ctx.md5_sha1.sha1)->val)
        _(assert state->hashState == (&state->hash_ctx.md5_sha1.md5)->val)
        _(ghost state->usable = (&state->hash_ctx.md5_sha1.md5)->usable)
        break;
    default:
        //S2N_ERROR(S2N_ERR_HASH_INusable_ALGORITHM);
        _(assert 0)
    }

    if (r == 0) {
        //S2N_ERROR(S2N_ERR_HASH_DIGEST_FAILED);
        _(assert 0)
    }
    _(wrap state)
    return 0;
}

int s2n_hash_reset(struct s2n_hash_state *state)
{
    _(ghost hash_state_destroy(state))
    return s2n_hash_init(state,state->alg);
}

int s2n_hash_copy(struct s2n_hash_state *to, struct s2n_hash_state *from)
{
    _(assert \wrapped_with_deep_domain(from))
    _(ghost hash_state_destroy(from))
    _(assert sizeof(struct s2n_hash_state) ==> to != NULL)
    *to = *from; //USER ADDED IN PLACE OF MEMCPY
    //memcpy_check(to, from, sizeof(struct s2n_hash_state));
    if(from->alg == S2N_HASH_NONE) {
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx})
    }
    else if(from->alg == S2N_HASH_MD5) {
        _(wrap &to->hash_ctx.md5)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.md5, &to->hash_ctx})
    }
    else if(from->alg == S2N_HASH_SHA1) {
        _(wrap &to->hash_ctx.sha1)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha1, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA224) {
        _(wrap &to->hash_ctx.sha224)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha224, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA256) {
        _(wrap &to->hash_ctx.sha256)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha256, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA384) {
        _(wrap &to->hash_ctx.sha384)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha384, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_SHA512) { 
        _(wrap &to->hash_ctx.sha512)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.sha512, &to->hash_ctx})}
    else if(from->alg == S2N_HASH_MD5_SHA1) {
        _(wrap &to->hash_ctx.md5_sha1.sha1)
        _(wrap &to->hash_ctx.md5_sha1.md5)
        _(wrap &to->hash_ctx.md5_sha1)
        _(wrap &to->hash_ctx)
        _(ghost to->\owns = {&to->hash_ctx.md5_sha1, &to->hash_ctx.md5_sha1.sha1, &to->hash_ctx.md5_sha1.md5, &to->hash_ctx})}
    else {_(assert 0)}
    _(wrap to)
    return 0;
}
