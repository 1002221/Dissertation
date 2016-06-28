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
 * on an "AS IS" BASIS, WITHoutt WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

//#pragma once

#include <stdint.h>
#include <stdlib.h>
#include <vcc.h>
#include "myblob.h"
#include "mymem.h"
#include <limits.h>

#define notnull_check( ptr )           do { if ( (ptr) == NULL ) { return -1; } } while(0)
#define memcpy_check( d, s, n )     do { if ( (n) ) { notnull_check( (d) ); memcpy( (d), (s), (n)); } } while(0)
#define memset_check( d, c, n )     do { if ( (n) ) { notnull_check( (d) ); memset( (d), (c), (n)); } } while(0)
#define GUARD( x )      if ( (x) < 0 ) return -1
#define SYSTEM_PAGE_SIZE() 394857

_(dynamic_owns) struct s2n_stuffer {
	/* The data for the s2n_stuffer */
	struct s2n_blob blob;

	/* Cursors to the current read/write position in the s2n_stuffer */
	uint32_t read_cursor;
	uint32_t write_cursor;

	/* The total size of the data segment */
	/* Has the stuffer been wiped? */
	unsigned int wiped:1;

	/* Was this stuffer alloc()'d ? */
	unsigned int alloced:1;

	/* Is this stuffer growable? */
	unsigned int growable:1;

	/* A growable stuffer can also be temporarily tainted */
	unsigned int tainted:1;

	_(invariant \mine(&blob))
	_(invariant read_cursor <= write_cursor && write_cursor <= \this->blob.size)
	//_(invariant !alloced ==> read_cursor == 0 && write_cursor == 0)
	//TODO: ADD INVARIANTS FOR WIPED, TAINTED, ETC)
	//_(invariant wiped ==> (\forall size_t i; i< blob.size ==> blob.data[i]==0))
}s2n_stuffer;


#define s2n_stuffer_data_available( s )   ((s)->write_cursor - (s)->read_cursor)
#define s2n_stuffer_space_remaining( s )  ((s)->blob.size - (s)->write_cursor)

/* Initialize and destroying stuffers */
extern int s2n_stuffer_init(struct s2n_stuffer *stuffer, struct s2n_blob *in)
	_(requires \mutable(stuffer))
	_(requires \wrapped(in))
	_(requires in->size > 0)
	//_(writes in == &stuffer->blob ? \span(stuffer) : {})
	_(writes in != &stuffer->blob ? {} : \extent(stuffer))
	_(writes in)
	_(ensures \wrapped(stuffer) && (in != &stuffer->blob ==> \mutable(in)))
	_(requires in->size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures stuffer->blob.size == \old(in->size))
	_(ensures \unchanged(in->size))
	_(ensures \result <= 0)
	//_(ensures \forall size_t i; i<in->size ==> stuffer->blob.val[i] == in->data[i])
	_(ensures stuffer->wiped && !stuffer->alloced && !stuffer->growable && !stuffer->tainted )
	_(ensures stuffer->read_cursor==stuffer->write_cursor && stuffer->write_cursor==0)
;

/*extern int s2n_stuffer_init(struct s2n_stuffer *stuffer, struct s2n_blob *in)
{
	_(assume in != &stuffer->blob)
	_(unwrap in)
	stuffer->blob.data = in->data;
	stuffer->blob.size = in->size;
	stuffer->wiped = 1;
	stuffer->alloced = 0;
	stuffer->growable = 0;
	stuffer->tainted = 0;
	stuffer->read_cursor = 0;
	stuffer->write_cursor = 0;
	stuffer->blob.allocated = in->allocated;
	stuffer->blob.user_allocated = 1;
	wrap_stuffer(stuffer);
	return 0;
}
*/
extern int s2n_stuffer_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes \extent(stuffer))
	_(requires \extent_mutable(stuffer))
	_(requires size>0)
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result <=0)
	_(ensures \result || (\wrapped(stuffer) && stuffer->blob.size == size))
	_(ensures !\result ==> stuffer->alloced && stuffer->blob.user_allocated)
	_(ensures !\result ==> stuffer->read_cursor==stuffer->write_cursor && stuffer->write_cursor==0) //follows from init
;
/*
int s2n_stuffer_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
{

	GUARD(s2n_alloc(&stuffer->blob, size));
	_(assert (&stuffer->blob)->size == size)
	GUARD(s2n_stuffer_init(stuffer, &stuffer->blob)); //surely this proves that init can't require stuffer to be extent mutable?
	_(unwrap stuffer)
	stuffer->alloced = 1;
	_(ghost (&(stuffer->blob))->\owns = {((uint8_t[stuffer->blob.allocated]) stuffer->blob.data)};)
	_(wrap &(stuffer->blob))
	_(assert stuffer->read_cursor <= stuffer->write_cursor && stuffer->write_cursor <= stuffer->blob.size)
	_(ghost stuffer->\owns = {&(stuffer->blob)})
	_(assert \inv(stuffer))
	_(wrap stuffer)
    return 0;
}*/

extern int s2n_stuffer_growable_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes \extent(stuffer))
	_(requires \extent_mutable(stuffer))
	_(requires size>0 && size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result || (\wrapped(stuffer) && stuffer->blob.size == size))
	_(ensures !\result ==> stuffer->growable && stuffer->alloced)
	_(ensures !\result ==> stuffer->read_cursor==stuffer->write_cursor && stuffer->write_cursor==0)
;

int s2n_stuffer_growable_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
{
    GUARD(s2n_stuffer_alloc(stuffer, size));
	_(unwrap stuffer)
    stuffer->growable = 1;
	_(wrap stuffer) 
    return 0;
}

extern int s2n_stuffer_free(struct s2n_stuffer *stuffer)
	//_(requires memory_initialized())
	_(requires \wrapped(stuffer))
	_(writes stuffer)
	_(ensures !\result ==> \extent_mutable(stuffer))
	_(ensures !\result && stuffer->alloced ==> stuffer->blob.size == 0)
;

int s2n_stuffer_free(struct s2n_stuffer *stuffer)
{
    if (stuffer->alloced == 0) {
		_(unwrap stuffer)
		_(unwrap &stuffer->blob)
        return 0;
    }
    if (stuffer->wiped == 0) {
        GUARD(s2n_stuffer_wipe(stuffer));
    }
	_(unwrap stuffer)
    GUARD(s2n_free(&stuffer->blob));

    stuffer->blob.data = NULL;
    stuffer->blob.size = 0;
    return 0;
}

extern int s2n_stuffer_resize(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes stuffer)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer))
	_(requires size > 0 && size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result <= 0)
	_(ensures !\result ==> (stuffer->blob.size == size))
	_(ensures !\result && size >= \old(stuffer->blob.size) ==> \unchanged(stuffer->read_cursor) && \unchanged(stuffer->write_cursor))
	_(ensures !\result && size < \old(stuffer->blob.size) ==> stuffer->write_cursor == \old(stuffer->write_cursor) - min(\old(stuffer->blob.size) - size, \old(stuffer->write_cursor)))
	_(ensures !\result && size < \old(stuffer->blob.size) ==> stuffer->read_cursor == min(\old(stuffer->read_cursor), stuffer->write_cursor))
;

extern int s2n_stuffer_resize(struct s2n_stuffer *stuffer, const uint32_t size)
{
    if (stuffer->growable == 0) {
        //S2N_ERROR(S2N_ERR_RESIZE_STATIC_STUFFER);
		return -1;
    }
    if (stuffer->tainted == 1) {
        //S2N_ERROR(S2N_ERR_RESIZE_TAINTED_STUFFER);
		return -1;
    }
    if (size == stuffer->blob.size) {
        return 0;
    }
	
    if (size < stuffer->blob.size) {
        GUARD(s2n_stuffer_wipe_n(stuffer, stuffer->blob.size - size));
	}
	_(unwrap stuffer)
    GUARD(s2n_realloc(&stuffer->blob, size));
	_(unwrap &stuffer->blob)
    stuffer->blob.size = size;
	stuffer->blob.user_allocated = 1;
	_(wrap &(stuffer->blob)) 
	_(wrap stuffer) 
    return 0;
}

extern int s2n_stuffer_reread(struct s2n_stuffer *stuffer)
	_(maintains \wrapped(stuffer))
	_(writes stuffer)
	_(ensures stuffer->read_cursor == 0 && \unchanged(stuffer->write_cursor))
;

extern int s2n_stuffer_reread(struct s2n_stuffer *stuffer)
{
	_(unwrap stuffer)
    stuffer->read_cursor = 0;
	_(wrap stuffer)
    return 0;
}

extern int s2n_stuffer_rewrite(struct s2n_stuffer *stuffer)
	_(writes stuffer)
	_(maintains \wrapped(stuffer))
	_(ensures stuffer->read_cursor == stuffer->write_cursor && stuffer->write_cursor == 0)
;

extern int s2n_stuffer_rewrite(struct s2n_stuffer *stuffer)
{
	_(unwrap stuffer)
    stuffer->write_cursor = 0;
    if (stuffer->read_cursor > stuffer->write_cursor) {
        stuffer->read_cursor = stuffer->write_cursor;
    }
	_(wrap stuffer)
    return 0;
}

extern int s2n_stuffer_wipe(struct s2n_stuffer *stuffer)
	_(writes stuffer)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer))
	_(ensures !\result ==> stuffer->tainted==0)
	_(ensures \result <= 0)
	//_(ensures \forall size_t i; i<stuffer->write_cursor ==> stuffer->blob.val[i]== 0)
	_(ensures !\result ==> (stuffer->write_cursor == stuffer->read_cursor && stuffer->write_cursor == 0)) 
;

int s2n_stuffer_wipe(struct s2n_stuffer *stuffer)
{
	_(unwrap stuffer)
    stuffer->tainted = 0;
	_(wrap stuffer)
    return s2n_stuffer_wipe_n(stuffer, stuffer->write_cursor);
}

extern int s2n_stuffer_wipe_n(struct s2n_stuffer *stuffer, const uint32_t n)
	_(writes stuffer)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer))
	//_(ensures \forall size_t i; i>= stuffer->write_cursor - min(n,stuffer->write_cursor) && i<stuffer->write_cursor
	//	==> stuffer->blob.val[i] == 0)
	_(ensures !\result ==> \unchanged(stuffer->tainted))
	_(ensures \result <= 0)
	_(ensures !\result ==> (stuffer->write_cursor == 0 ==> stuffer->wiped))
	_(ensures !\result ==> stuffer->write_cursor == \old(stuffer->write_cursor) - min(n, \old(stuffer->write_cursor)) && 
		stuffer->read_cursor == min(\old(stuffer->read_cursor), stuffer->write_cursor))
;

int s2n_stuffer_wipe_n(struct s2n_stuffer *stuffer, const uint32_t size)
{
    uint32_t n = size;
	if (stuffer->write_cursor < n) {
        n = stuffer->write_cursor;
    }

    // Use '0' instead of 0 precisely to prevent C string compatibility 
	_(unwrap stuffer)
	_(unwrap &stuffer->blob)
    memset/*_check*/(stuffer->blob.data + stuffer->write_cursor - n, '0', n);
    stuffer->write_cursor -= n;

    if (stuffer->write_cursor == 0) {
        stuffer->wiped = 1;
    }
    if (stuffer->write_cursor < stuffer->read_cursor) {
        stuffer->read_cursor = stuffer->write_cursor;
    }
	_(ghost stuffer->blob.val = \lambda size_t i; stuffer->blob.data[i];) 
	_(wrap &(stuffer->blob)) 
	_(wrap stuffer) 
	return 0;
}

/* Basic read and write */
extern int s2n_stuffer_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
	_(requires \wrapped(outt))
	_(requires outt->size > 0 && outt->size <= s2n_stuffer_data_available(stuffer))
	_(writes outt)
	_(writes stuffer)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer) && \wrapped(outt))
	_(ensures \result <= 0)
	_(ensures !\result ==> \unchanged(stuffer->write_cursor) && stuffer->read_cursor == \old(stuffer->read_cursor)+outt->size)
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == stuffer->blob.val[i])
;

int s2n_stuffer_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
{
	//notnull_check(outt);
	_(unwrap outt)
	_(unwrap blob_data(outt))
	{ int res = s2n_stuffer_read_bytes(stuffer, outt->data, outt->size); _(wrap blob_data(outt)) wrap_blob(outt); return res; }
}

extern int s2n_stuffer_read_bytes(struct s2n_stuffer *stuffer, uint8_t *outt, uint32_t n)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer))
	_(requires \thread_local_array(outt,n))
	_(writes \array_range(outt,n), stuffer)
	_(requires n <= s2n_stuffer_data_available(stuffer))
	_(ensures \result <= 0)
	//_(ensures \forall size_t i; i<n ==> outt[i] == stuffer->blob.val[i])
	_(ensures !\result ==> \unchanged(stuffer->write_cursor) && stuffer->read_cursor==\old(stuffer->read_cursor)+n)
;

extern int s2n_stuffer_read_bytes(struct s2n_stuffer *stuffer, uint8_t *data, uint32_t size)
{
	GUARD(s2n_stuffer_skip_read(stuffer, size));
	_(unwrap stuffer)
	_(unwrap &stuffer->blob)
	void *ptr = stuffer->blob.data + stuffer->read_cursor - size;
	//notnull_check(ptr);
	
	memcpy/*_check*/(data, ptr, size);
	_(ghost stuffer->blob.val = \lambda size_t i; stuffer->blob.data[i];) 
	_(wrap &(stuffer->blob)) 
	_(wrap stuffer) 
	return 0;
}

extern int s2n_stuffer_skip_read(struct s2n_stuffer *stuffer, uint32_t n)
	_(requires \wrapped(stuffer))
	_(ensures \wrapped(stuffer))
	_(writes stuffer)
	_(ensures \result <= 0)
	_(requires n <= s2n_stuffer_data_available( stuffer ))
	_(ensures stuffer->read_cursor == \old(stuffer->read_cursor)+n && \unchanged(stuffer->write_cursor))
;

int s2n_stuffer_skip_read(struct s2n_stuffer *stuffer, uint32_t n)
{
    //if (s2n_stuffer_data_available(stuffer) < n) {
    //    S2N_ERROR(S2N_ERR_STUFFER_outt_OF_DATA);
    //}
	_(unwrap stuffer)
    stuffer->read_cursor += n;
	_(wrap stuffer)
    return 0;
}

extern int s2n_stuffer_erase_and_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
	_(requires \wrapped(outt) && \wrapped(stuffer))
	_(requires outt->size > 0 && outt->size <= s2n_stuffer_data_available(stuffer))
	_(writes outt, stuffer)
	_(ensures !\result ==> \wrapped(stuffer))
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == \old(stuffer->blob.val[i]))
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == 0)
	_(ensures !\result ==> \unchanged(stuffer->write_cursor) && stuffer->read_cursor == \old(stuffer->read_cursor)+outt->size)
;

int s2n_stuffer_erase_and_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
{
	/*GUARD(*/s2n_stuffer_skip_read(stuffer, outt->size)/*)*/;
	
	_(unwrap stuffer)
	_(unwrap &stuffer->blob)
    void *ptr = stuffer->blob.data + stuffer->read_cursor - outt->size;
    //if (ptr == NULL) {return -1;}
	_(unwrap outt)
	_(unwrap blob_data(outt))
    memcpy/*_check*/(outt->data, ptr, outt->size);
    memset(ptr, 0, outt->size);
	_(wrap blob_data(outt))
	_(wrap outt)
	_(ghost stuffer->blob.val = \lambda size_t i; stuffer->blob.data[i];) 
	_(wrap &(stuffer->blob)) 
	_(wrap stuffer) 
    return 0;
}


extern int s2n_stuffer_write(struct s2n_stuffer *stuffer, const struct s2n_blob *in)
	_(requires \wrapped(in) && \wrapped(stuffer))
	_(requires in->size > 0 && in->size <= s2n_stuffer_space_remaining(stuffer))
	_(requires stuffer->blob.size + max(in->size, 1024) < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures !\result ==> \wrapped(in) && \wrapped(stuffer))
	_(writes stuffer, in)
	_(ensures \result <= 0)
	//_(ensures \forall size_t i; i<in->size ==> in->val[i] == stuffer->blob.val[i])
	_(ensures !\result ==> (stuffer->write_cursor == \old(stuffer->write_cursor) + in->size && \unchanged(stuffer->read_cursor)))
;

int s2n_stuffer_write(struct s2n_stuffer *stuffer, const struct s2n_blob *in)
{
	_(unwrap in)
	_(unwrap blob_data(in))
	{ int res = s2n_stuffer_write_bytes(stuffer, in->data, in->size); _(wrap blob_data(in)) wrap_blob(in); return res; }
}

extern int s2n_stuffer_write_bytes(struct s2n_stuffer *stuffer, const uint8_t *in, const uint32_t n)
	_(requires \wrapped(stuffer) && \thread_local_array(in,n))
	_(ensures !\result ==> \wrapped(stuffer))
	_(requires stuffer->blob.size + max(n, 1024) < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(writes \array_range(in,n), stuffer)
	_(requires n>0 && n <= s2n_stuffer_space_remaining(stuffer))
	_(ensures \result <= 0)
	//_(ensures \forall size_t i; i<n ==> in[i] == stuffer->blob.val[i])
	_(ensures !\result ==> (stuffer->write_cursor == \old(stuffer->write_cursor) + n && \unchanged(stuffer->read_cursor)))
;

int s2n_stuffer_write_bytes(struct s2n_stuffer *stuffer, const uint8_t *data, const uint32_t size)
{
	GUARD(s2n_stuffer_skip_write(stuffer, size));
	_(unwrap stuffer)
	_(unwrap &stuffer->blob)

	void *ptr = stuffer->blob.data + stuffer->write_cursor - size;
	//if (ptr == NULL) {return -1;}

	if (ptr == data) {
		_(wrap &(stuffer->blob)) 
		_(wrap stuffer) 
		return 0;
	}

	memcpy/*_check*/(ptr, data, size);
	_(ghost stuffer->blob.val = \lambda size_t i; stuffer->blob.data[i];) 
	_(wrap &(stuffer->blob)) 
	_(wrap stuffer) 
	return 0;
}

extern int s2n_stuffer_skip_write(struct s2n_stuffer *stuffer, const uint32_t n)
	_(requires \wrapped(stuffer))
	_(ensures !\result ==> \wrapped(stuffer))
	_(writes stuffer)
	_(requires stuffer->blob.size + max(n, 1024) < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(requires stuffer->write_cursor + n < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result <= 0)
	_(requires n <= s2n_stuffer_space_remaining( stuffer ) || stuffer->growable)
	_(ensures !\result && stuffer->growable && n > \old(s2n_stuffer_space_remaining(stuffer)) ==> stuffer->blob.size == \old(stuffer->blob.size) + max(n,1024))
	_(ensures !\result ==> (stuffer->write_cursor == \old(stuffer->write_cursor)+n && \unchanged(stuffer->read_cursor)))
;


int s2n_stuffer_skip_write(struct s2n_stuffer *stuffer, const uint32_t n)
{
	if (s2n_stuffer_space_remaining(stuffer) < n) {
		if (stuffer->growable) {
			/* Always grow a stuffer by at least 1k */
			uint32_t growth = max(n, 1024);
	
			GUARD(s2n_stuffer_resize(stuffer, stuffer->blob.size + growth));
		} else {
			//S2N_ERROR(S2N_ERR_STUFFER_IS_FULL);
			return -1;
		}
	}
	_(unwrap stuffer)
	stuffer->write_cursor += n;
	stuffer->wiped = 0;
        _(wrap stuffer)
	return 0;
}

/* Raw read/write move the cursor along and give you a pointer you can
 * read/write data_len bytes from/to in-place.
 */
extern void *s2n_stuffer_raw_write(struct s2n_stuffer *stuffer, const uint32_t data_len)
	_(writes \extent(stuffer))
	_(maintains \wrapped(stuffer))
	_(requires data_len<=s2n_stuffer_space_remaining(stuffer))
	_(ensures !\result ==> stuffer->tainted)
	_(ensures !\result ==> (stuffer->write_cursor==\old(stuffer->write_cursor) + data_len && stuffer->read_cursor == \old(stuffer->read_cursor)))
;

extern void *s2n_stuffer_raw_read(struct s2n_stuffer *stuffer, uint32_t data_len)
	_(writes stuffer)
	_(requires data_len <= s2n_stuffer_data_available( stuffer ))
	_(maintains \wrapped(stuffer))
	_(ensures !\result ==> stuffer->tainted)
	_(ensures !\result ==> (stuffer->read_cursor==\old(stuffer->read_cursor) + data_len && stuffer->write_cursor == \old(stuffer->write_cursor)))
;

/* Send/receive stuffer to/from a file descriptor */
extern int s2n_stuffer_recv_from_fd(struct s2n_stuffer *stuffer, int rfd, uint32_t len);
extern int s2n_stuffer_send_to_fd(struct s2n_stuffer *stuffer, int wfd, uint32_t len);

/* Read and write integers in network order */
extern int s2n_stuffer_read_uint8(struct s2n_stuffer *stuffer, uint8_t *u);
extern int s2n_stuffer_read_uint16(struct s2n_stuffer *stuffer, uint16_t *u);
extern int s2n_stuffer_read_uint24(struct s2n_stuffer *stuffer, uint32_t *u);
extern int s2n_stuffer_read_uint32(struct s2n_stuffer *stuffer, uint32_t *u);
extern int s2n_stuffer_read_uint64(struct s2n_stuffer *stuffer, uint64_t *u);

extern int s2n_stuffer_write_uint8(struct s2n_stuffer *stuffer, const uint8_t u);
extern int s2n_stuffer_write_uint16(struct s2n_stuffer *stuffer, const uint16_t u);
extern int s2n_stuffer_write_uint24(struct s2n_stuffer *stuffer, const uint32_t u);
extern int s2n_stuffer_write_uint32(struct s2n_stuffer *stuffer, const uint32_t u);
extern int s2n_stuffer_write_uint64(struct s2n_stuffer *stuffer, const uint64_t u);

/* Copy one stuffer to another */
extern int s2n_stuffer_copy(struct s2n_stuffer *from, struct s2n_stuffer *to, uint32_t len)
	_(requires \wrapped(from) && \wrapped(to))
	_(requires to != from)
	_(requires len <= s2n_stuffer_space_remaining(to) || to->growable)
	_(requires to->write_cursor + len < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(requires to->blob.size + max(len, 1024) < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures !\result ==> \wrapped(from) && \wrapped(to))
	_(writes to, from)
	_(requires len<=s2n_stuffer_data_available(from))
	_(ensures !\result ==> (\unchanged(from->write_cursor) && from->read_cursor == \old(from->read_cursor)+len && \unchanged(to->read_cursor) && to->write_cursor == \old(to->write_cursor)+len))
;

int s2n_stuffer_copy(struct s2n_stuffer *from, struct s2n_stuffer *to, const uint32_t len)
{
	GUARD(s2n_stuffer_skip_read(from, len));
	GUARD(s2n_stuffer_skip_write(to, len));
	_(unwrap from)
	_(unwrap &from->blob)
	_(unwrap to)
	_(unwrap &to->blob)
	uint8_t *from_ptr = from->blob.data + from->read_cursor - len;
	uint8_t *to_ptr = to->blob.data + to->write_cursor - len;

	memcpy/*_check*/(to_ptr, from_ptr, len);
	_(ghost from->blob.val = \lambda size_t i; from->blob.data[i];) 
	_(wrap &(from->blob)) 
	_(wrap from) 
	_(ghost to->blob.val = \lambda size_t i; to->blob.data[i];) 
	_(wrap &(to->blob)) 
	_(wrap to) 
	return 0;
}

/* Read and write base64 */
extern int s2n_stuffer_read_base64(struct s2n_stuffer *stuffer, struct s2n_stuffer *outt);
extern int s2n_stuffer_write_base64(struct s2n_stuffer *stuffer, struct s2n_stuffer *in);

/* Useful for text manipulation ... */
#define s2n_stuffer_write_char( stuffer, c )  s2n_stuffer_write_uint8( (stuffer), (uint8_t) (c) )
#define s2n_stuffer_read_char( stuffer, c )  s2n_stuffer_read_uint8( (stuffer), (uint8_t *) (c) )
#define s2n_stuffer_write_str( stuffer, c )  s2n_stuffer_write_bytes( (stuffer), (const uint8_t *) (c), strlen((c)) )
#define s2n_stuffer_write_text( stuffer, c, n )  s2n_stuffer_write_bytes( (stuffer), (const uint8_t *) (c), (n) )
#define s2n_stuffer_read_text( stuffer, c, n )  s2n_stuffer_read_bytes( (stuffer), (uint8_t *) (c), (n) )
extern int s2n_stuffer_peek_char(struct s2n_stuffer *stuffer, char *c);
extern int s2n_stuffer_read_token(struct s2n_stuffer *stuffer, struct s2n_stuffer *token, char delim);
extern int s2n_stuffer_skip_whitespace(struct s2n_stuffer *stuffer);
extern int s2n_stuffer_alloc_ro_from_string(struct s2n_stuffer *stuffer, const char *str);

/* Read an RSA private key from a PEM encoded stuffer to an ASN1/DER encoded one */
extern int s2n_stuffer_rsa_private_key_from_pem(struct s2n_stuffer *pem, struct s2n_stuffer *asn1);

/* Read a certificate  from a PEM encoded stuffer to an ASN1/DER encoded one */
extern int s2n_stuffer_certificate_from_pem(struct s2n_stuffer *pem, struct s2n_stuffer *asn1);

/* Read DH parameters om a PEM encoded stuffer to a PKCS3 encoded one */
extern int s2n_stuffer_dhparams_from_pem(struct s2n_stuffer *pem, struct s2n_stuffer *pkcs3);

