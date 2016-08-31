#include "s2n_hmac.h"
#include "myblob.h"
#include <stdlib.h>

#define SYSTEM_PAGE_SIZE() 394857

int s2n_alloc(struct s2n_blob *b, uint32_t size)
    _(writes \extent(b))
    _(requires size && size < _UI32_MAX - SYSTEM_PAGE_SIZE())
    _(ensures \wrapped(b) && b->size == size)
;

int wrap_blob_data(uint8_t *data, uint32_t size)
    _(writes \array_range(data,size))
    _(ensures \wrapped((uint8_t[size])data))
    ;

int testing()
{
    /*initialise the data with which to initalise the blobs, which will be used to initialise, update and store digested data
    from hmac states*/
    uint32_t size = 50;
    uint32_t size1 = 20;
    uint32_t size2 = 20; //constrained to be equal to the digest size corresponding to the algorithm

    /*initialise blobs*/
    struct s2n_blob *key = malloc(sizeof(*key));
    if(key==NULL) return -1;
    s2n_alloc(key,size);
    struct s2n_blob *m = malloc(sizeof(*m));
    if(m==NULL) return -1;
    s2n_alloc(m,size1);
    struct s2n_blob *outt = malloc(sizeof(*outt));
    if(outt==NULL) return -1;
    s2n_alloc(outt,size2);

    /*choose an algorithm, initalise hmac state*/
    struct s2n_hmac_state *state = malloc(sizeof(*state));
    if(state==NULL) return -1;
    s2n_hmac_algorithm r = S2N_HMAC_SHA1;
    _(assert \wrapped_with_deep_domain(key)) //used to prove that key->data and key->size form a thread-local array
    GUARD(s2n_hmac_init(state,r,key->data,key->size)); 
    _(assert key->size>block_size_alg(r) ==> state->message == repeat(0x0,0))
    
    /*update with data (can be called repeatedly*/   
    _(assert \wrapped_with_deep_domain(m))
    GUARD(s2n_hmac_update(state,m->data,m->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> state->message == make_num(m->data,m->size))
    
    /*digest HMAC of message*/
    _(assert \wrapped_with_deep_domain(outt))
    _(unwrap outt)
    _(unwrap blob_data(outt))
    GUARD(s2n_hmac_digest(state,outt->data,outt->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> make_num(outt->data,outt->size) == 
        hashVal(concatenate(xor(num_resize(hashVal(make_num(key->data,key->size),hmac_to_hash(r)),block_size_alg(r)),
        repeat(0x5c,block_size_alg(r))),
        hashVal(concatenate(xor(num_resize(hashVal(make_num(key->data,key->size),hmac_to_hash(state->alg)),state->block_size),
        repeat(0x36,state->block_size)),make_num(m->data,m->size)),hmac_to_hash(r))),
        hmac_to_hash(r)))
    _(assert key->size<=block_size_alg(r) ==> make_num(outt->data,outt->size) == 
        hashVal(concatenate(xor(num_resize(make_num(key->data,key->size),block_size_alg(r)),
        repeat(0x5c,block_size_alg(r))),
        hashVal(concatenate(xor(num_resize(make_num(key->data,key->size),state->block_size),
        repeat(0x36,state->block_size)),make_num(m->data,m->size)),hmac_to_hash(r))),
        hmac_to_hash(r)))
    /* what we end up writing to outt with can be seen to be equal to H((K' XOR 0X5C) || H((K' XOR 0X36) || M)), 
    where M is the message, K' is the key (hashed or with 0s appended to be the same length as the digest size), and 
    H is the hash function. */
}


/*
int testing()
{
    /*initialise the data with which to initalise the blobs, which will be used to initialise, update and store digested data
    from hmac states*//*
    uint32_t size = 20;
    uint32_t size1 = 20;
    uint32_t size2 = 20;
    uint8_t *data = malloc(sizeof (uint8_t) *size);
    _(wrap &data)
    uint8_t *data1 = malloc(sizeof (uint8_t) * size1);
    uint8_t *data2 = malloc(sizeof (uint8_t) * size2);

    /*initialise blobs*//*
    struct s2n_blob *key = malloc(sizeof(*key));
    if(key==NULL) return -1;
    s2n_blob_init(key,data,size);
    struct s2n_blob *b = malloc(sizeof(*b));
    if(b==NULL) return -1;
    s2n_blob_init(b,data1,size1);
    struct s2n_blob *outt = malloc(sizeof(*outt));
    if(outt==NULL) return -1;
    s2n_blob_init(outt,data2,size2);

    /*choose an algorithm, initalise hmac state*//*
    struct s2n_hmac_state *state = malloc(sizeof(*state));
    if(state==NULL) return -1;
    s2n_hmac_algorithm r = S2N_HMAC_SSLv3_SHA1;
    _(assert \wrapped_with_deep_domain(key))
    GUARD(s2n_sslv3_mac_init(state,r,key->data,key->size)); 
    _(assert state->message == repeat(0x0,0))
    
    /*update with data (can be called repeatedly*/  /*  
    GUARD(s2n_hmac_update(state,b->data,b->size));
    _(assert \inv(state))
    _(assert key->size>block_size_alg(r) ==> state->message == make_num(b->data,b->size))
    
    /*digest HMAC of message*//*
    GUARD(s2n_hmac_digest(state,outt->data,outt->size));
    _(assert \inv(state))
    _(assert make_num(outt->data,outt->size) == 
        hashVal(concatenate(concatenate(state->key,repeat(0x5c,state->block_size)),
        hashVal(concatenate(concatenate(state->key,repeat(0x36,state->block_size)),state->message),
        hmac_to_hash(state->alg))),hmac_to_hash(state->alg)))

    /* slightly differently, what we end up writing to outt with can be seen to be equal to 
    H((K || 0X5C) || H((K || 0X36) || M)) *//*
}*/
