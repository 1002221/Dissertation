#include "s2n_hmac.h"
#include <stdlib.h>

#define SYSTEM_PAGE_SIZE() 394857

int s2n_alloc(struct s2n_blob *b, uint32_t size)
    _(writes \extent(b))
    _(requires size && size < _UI32_MAX - SYSTEM_PAGE_SIZE())
    _(ensures \wrapped(b) && b->size == size)
;

_(dynamic_owns) struct s2n_blob {
	// Abstract value
	_(ghost uint8_t val[size_t])
	uint32_t size;
	// true iff the backing memory was provided by the user and is to be returned to him
	BOOL user_allocated;
	BOOL mlocked;
	// if user_allocated, the size and address of the backing memory (but not the data) is part of the abstract value
	uint32_t allocated;
	uint8_t *data;
 
	// Coupling invariant
	_(invariant \forall size_t i; i < size ==> val[i] == data[i])
    //_(invariant val == (\lambda size_t i; i<size? data[i] : (uint8_t)0x0)) 
	// other data invariants
	_(invariant size && size <= allocated)
	_(invariant allocated ==> \mine(blob_data(\this)))
	_(invariant user_allocated || !allocated || \malloc_root(blob_data(\this))) //if it's not the root object, then the only way it could have been allocated is if it was user-allocated.
	_(invariant mlocked == 0)
}s2n_blob;

#define M state->message

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
    s2n_alloc(key, size);
    struct s2n_blob *m = malloc(sizeof(*m));
    if(m==NULL) return -1;
    s2n_alloc(m, size1);
    struct s2n_blob *outt = malloc(sizeof(*outt));
    if(outt==NULL) return -1;
    s2n_alloc(outt, size2);

    /*choose an algorithm, initalise hmac state*/
    struct s2n_hmac_state *state = malloc(sizeof(*state));
    if(state==NULL) return -1;
    s2n_hmac_algorithm r = S2N_HMAC_SHA1;
    _(assert \wrapped_with_deep_domain(key)) //used to prove that key->data and key->size form a thread-local array
    GUARD(s2n_hmac_init(state, r, key->data, key->size)); 
    _(assert key->size>L ==> M == repeat(0x0, 0))
    
    /*update with data (can be called repeatedly*/   
    _(assert \wrapped_with_deep_domain(m))
    GUARD(s2n_hmac_update(state, m->data, m->size));
    _(assert \inv(state))
    _(assert key->size>L ==> M == make_num(m->data, m->size))
    
    /*digest HMAC of message*/
    _(assert \wrapped_with_deep_domain(outt))
    _(unwrap outt)
    _(unwrap blob_data(outt))
    GUARD(s2n_hmac_digest(state, outt->data, outt->size));
    _(assert \inv(state))
    _(assert key->size>L ==> make_num(outt->data,  outt->size) == H1(concatenate(xor(Kprime2, OPAD), 
        H(concatenate(xor(Kprime2, IPAD), M)))))
    _(assert key->size<=L ==> make_num(outt->data, outt->size) == H1(concatenate(xor(Kprime, OPAD), 
        H(concatenate(xor(Kprime, IPAD), M)))))
    /* what we end up writing to outt with can be seen to be equal to H((K' XOR 0X5C) || H((K' XOR 0X36) || M)), 
    where M is the message, K' is the key (hashed or with 0s appended to be the same length as the digest size), and 
    H is the hash function. */
}
