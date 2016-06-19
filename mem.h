
#include <vcc.h>
#include <stdint.h>
#include "myblob.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SYSTEM_PAGE_SIZE() 394857
static uint32_t page_size = 4096;
/*#define _UI32_MAX UINT32_MAX
*/
/*_(pure) uint32_t minn(uint32_t a, uint32_t b) 
	_(requires \true) 
	_(ensures \result <= a && \result <= b) { 
		if (a <= b) return a; 
		else return b; 
} */

int s2n_alloc(struct s2n_blob *b, uint32_t size)
	_(writes \extent(b))
	_(requires size>0)
	_(requires \extent_mutable(b))
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result || (\wrapped(b) && b->size == size))
;
 
int s2n_realloc(struct s2n_blob *b, uint32_t size)
	_(requires \wrapped(b))
	_(ensures size ==> \wrapped(b))
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(writes b)
	//_(ensures \result <= 0)
	//_(ensures \unchanged(b->user_allocated))
	_(ensures \old(b->user_allocated) ==> \unchanged(b->allocated) && \unchanged(b->data))
	//_(ensures \result ==> size > b->size && \unchanged(b->size) && \unchanged(b->val))
	_(ensures \result == 0 ==> b->size == size)
	//_(ensures \forall size_t i; i < min(size, \old(b->size)) ==> \unchanged(b->val[i]))
;
 
int s2n_free(struct s2n_blob *b)
	//_(requires memory_initialized())
	_(requires \wrapped(b))
	_(writes b)
	_(ensures \mutable(b))
	_(ensures \unchanged(b->user_allocated))
	_(ensures \old(b->user_allocated && b->allocated) ==> \wrapped(\old(blob_data(b))))
	//_(ensures \old(b->user_allocated) ==> \forall size_t i; i < \old(b->size) ==> \old(b->data)[i] == \old(b->val[i]))
	_(ensures !\result ==> b->data == NULL && b->size == 0 && b->allocated == 0)
;

int s2n_free(struct s2n_blob *b)
{
	int munlock_rc = 0;
	/*if (b->mlocked) {
		munlock_rc = munlock(b->data, b->size);
	}*/
	_(unwrap b)
	//if(b->data != NULL) free(b->data);
	b->data = NULL;
	b->size = 0;
	b->allocated = 0;

	/*if (munlock_rc < 0) {
		S2N_ERROR(S2N_ERR_MUNLOCK);
	}*/
	b->mlocked = 0;

	return 0;
}

int s2n_realloc(struct s2n_blob *b, uint32_t size)
{
	if (b->user_allocated) {
		return -1;
	}
	_(unwrap b)
	if (size == 0) {
		wrap_blob(b);
		return s2n_free(b);
	}
	if (size < b->allocated && size != 0) {
		b->size = size;
		_(assert b->size <= b->allocated)
		wrap_blob(b);
		return 0;
    }
	uint32_t page_size = 4096;
	uint32_t allocate = page_size * ((size + (page_size - 1)) / page_size);
	void *data;
    /*if (posix_memalign(&data, page_size, allocate)) {
        S2N_ERROR(S2N_ERR_ALLOC);
    }*/
	//posix_memalign(&data, page_size, allocate);
	if (b->size) {
		//memcpy_check(data, b->data, b->size);
		if(b->size && data) memcpy(data,b->data,b->size);
		//GUARD(s2n_free(b));
		wrap_blob(b);
		s2n_free(b);
	}
	b->data = data; 
	b->size = size;
	b->allocated = allocate;
	
	/*#ifdef MADV_DONTDUMP
		if (madvise(b->data, size, MADV_DONTDUMP) < 0) {
			GUARD(s2n_free(b));
			S2N_ERROR(S2N_ERR_MADVISE);
		}
	#endif*/
	/*if (use_mlock == 0) {
		return 0;
	}*/

	/*if (mlock(b->data, size) < 0) {
		GUARD(s2n_free(b));
		S2N_ERROR(S2N_ERR_MLOCK);
	}*/
	b->mlocked = 1;
	b->user_allocated = 1;
	_(ghost { 
		b->val = \lambda size_t i; b->data[i]; 
		b->\owns = b->allocated ? {blob_data(b)} : {}; 
		_(assert \inv(b)) 
	})
	_(wrap b)
	return 0;
}
