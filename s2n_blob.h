#pragma once
#include <vcc.h>
#include <stdint.h>
#include <stdlib.h>

//#include <string.h>

uint8_t * memcpy(uint8_t *dst, uint8_t *src, size_t size)
       _(writes \array_range(dst,size))
       _(requires \thread_local_array(src,size))
       _(requires \arrays_disjoint(dst,size, src,size))
       _(ensures \forall size_t i; i < size ==> dst[i] == \old(src[i]))
       _(ensures \result == dst)
       _(decreases 0)
;

void *  memset(uint8_t * dst, uint8_t val, size_t size)
       _(requires \mutable_array(dst,size))
       _(writes \array_range(dst,size))
       _(ensures \forall size_t i; i < size ==> dst[i] == val)
       //_(ensures \result == dst)
;

typedef int BOOL;
#define TRUE ((int) 1)
#define FALSE ((int) 0)
 
// An s2n_blob represents an abstract array of uint8_t.
// It is either derived from a chunk of user-supplied memory, or free (in which case it manages its own).
// When a derived blob is destroyed, it returns to the owner the memory it was derived from.
 
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

_(def \object blob_data(struct s2n_blob *b) { return ((uint8_t[b->allocated]) b->data); })

#define wrap_blob(b) _(ghost { \
	b->val = \lambda size_t i; b->data[i]; \
	b->\owns = b->allocated ? {blob_data(b)} : {}; \
	_(assert \inv(b)) \
	_(wrap b) \
})
       
extern int s2n_blob_init(struct s2n_blob *b, uint8_t *data, uint32_t size)
	//_(requires \mutable(b))
	_(requires \wrapped((uint8_t[size]) data))
    _(writes \array_range(data,size))
	_(writes (uint8_t[size]) data)
	_(requires size>0)
	_(writes \span(b))
	_(ensures \wrapped(b) && b->size == size && b->allocated == size && b->user_allocated && b->data == data
		&& \forall size_t i; i < size ==> b->val[i] == \old(data[i]))
	_(ensures \result == 0)
;
 
extern int s2n_blob_zero(struct s2n_blob *b)
    _(requires \wrapped(b))
    _(requires b->size > 0 && b->data != NULL)
    _(requires b->user_allocated)
	_(requires b->size <= b->allocated)
    _(ensures !\result ==> \wrapped(b))
    _(writes b)
    _(ensures \unchanged(b->size) && \unchanged(b->allocated) && \unchanged(b->user_allocated) && \unchanged(b->data))
    //_(ensures !\result ==> \forall size_t i; i < b->size ==> b->val[i] == 0)
    _(ensures \result <= 0)
;

_(ghost int blob_destroy(struct s2n_blob *b)
    _(requires \wrapped(b))
    _(writes b)
    _(ensures \extent_mutable(b))
    _(ensures \extent_fresh(b))
;)