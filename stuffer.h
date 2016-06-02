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

//#pragma once

#include <stdint.h>
#include <stdlib.h>
#include <vcc.h>
#include "myblob.h"
//#include "mymem.h"
#include <limits.h>

#define SYSTEM_PAGE_SIZE() 394857
//#define _UI32_MAX UINT32_MAX

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
	//TODO: ADD INVARIANTS FOR WIPED, TAINTED, ETC)
	//_(invariant wiped ==> (\forall size_t i; i< blob.size ==> blob.data[i]==0))
}s2n_stuffer;


#define s2n_stuffer_data_available( s )   ((s)->write_cursor - (s)->read_cursor)
#define s2n_stuffer_space_remaining( s )  ((s)->blob.size - (s)->write_cursor)

/* Initialize and destroying stuffers */
extern int s2n_stuffer_init(struct s2n_stuffer *stuffer, struct s2n_blob *in)
	_(requires in->size ==> \extent_mutable(stuffer))
	_(requires \wrapped(in))
	_(writes in->size? \extent(stuffer) : {})
	_(ensures \wrapped(stuffer) && \wrapped(in))
	_(requires in->size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures stuffer->blob.size == in->size)
	_(ensures \forall size_t i; i<in->size ==> stuffer->blob.data[i] == in->data[i])
	_(ensures stuffer->wiped && !stuffer->alloced && !stuffer->growable && !stuffer->tainted && !stuffer->read_cursor && !stuffer->write_cursor && (\result == 0))
;

extern int s2n_stuffer_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes size? \extent(stuffer): {})
	_(requires size ==> \extent_mutable(stuffer))
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result || (\wrapped(stuffer) && stuffer->blob.size == size))
	_(ensures stuffer->alloced)
;

extern int s2n_stuffer_growable_alloc(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes size? \extent(stuffer): {})
	_(requires size ==> \extent_mutable(stuffer))
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures \result || (\wrapped(stuffer) && stuffer->blob.size == size))
	_(ensures stuffer->growable)
	_(ensures stuffer->alloced)
;

extern int s2n_stuffer_free(struct s2n_stuffer *stuffer)
	//_(requires memory_initialized())
	_(requires \wrapped(stuffer))
	_(writes stuffer)
	_(ensures \extent_mutable(stuffer))
	_(ensures stuffer->blob.size == 0 && !stuffer->blob.allocated)
;

extern int s2n_stuffer_resize(struct s2n_stuffer *stuffer, const uint32_t size)
	_(writes stuffer)
	_(maintains \wrapped(stuffer))
	_(requires stuffer->growable)
	_(requires stuffer->tainted)
	_(requires size < _UI32_MAX - SYSTEM_PAGE_SIZE())
	_(ensures stuffer->blob.size == size)
;

extern int s2n_stuffer_reread(struct s2n_stuffer *stuffer)
	_(maintains \wrapped(stuffer))
	_(requires \extent_mutable(stuffer))
	_(ensures stuffer->read_cursor == 0)
;

extern int s2n_stuffer_rewrite(struct s2n_stuffer *stuffer)
	_(writes stuffer)
	_(maintains \wrapped(stuffer))
	_(requires s2n_stuffer_space_remaining(stuffer))
	_(ensures stuffer->read_cursor == stuffer->write_cursor == 0)
;

extern int s2n_stuffer_wipe(struct s2n_stuffer *stuffer)
	_(writes stuffer)
	_(maintains \wrapped(stuffer))
	_(requires !stuffer->tainted)
	//_(ensures \forall size_t i; i<stuffer->write_cursor ==> stuffer->blob.val[i]== 0)
	_(ensures stuffer->write_cursor == \old(stuffer->write_cursor))
;

extern int s2n_stuffer_wipe_n(struct s2n_stuffer *stuffer, const uint32_t n)
	_(writes stuffer)
	_(maintains \wrapped(stuffer))
	//_(ensures \forall size_t i; i>= stuffer->write_cursor - min(n,stuffer->write_cursor) && i<stuffer->write_cursor
	//	==> stuffer->blob.val[i] == 0)
	_(ensures stuffer->write_cursor == \old(stuffer->write_cursor))
;

/* Basic read and write */
extern int s2n_stuffer_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
	_(requires \extent_mutable(outt))
	_(requires outt != NULL)
	_(requires outt->size <= s2n_stuffer_data_available(stuffer))
	_(writes \extent(outt))
	_(ensures \wrapped(outt))
	_(maintains \wrapped(stuffer))
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == stuffer->blob.val[i])
;

extern int s2n_stuffer_erase_and_read(struct s2n_stuffer *stuffer, struct s2n_blob *outt)
	_(requires \extent_mutable(outt))
	_(requires outt->size <= s2n_stuffer_data_available(stuffer))
	_(ensures \wrapped(outt))
	_(maintains \wrapped(stuffer))
	_(writes \extent(outt))
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == \old(stuffer->blob.val[i]))
	//_(ensures \forall size_t i; i<outt->size ==> outt->val[i] == 0)
;

extern int s2n_stuffer_write(struct s2n_stuffer *stuffer, const struct s2n_blob *in)
	_(maintains \wrapped(in))
	_(maintains \wrapped(stuffer))
	_(writes stuffer)
	_(requires in->size <= stuffer->blob.size)
	//_(ensures \forall size_t i; i<in->size ==> in->val[i] == stuffer->blob.val[i])
;

extern int s2n_stuffer_read_bytes(struct s2n_stuffer *stuffer, uint8_t *outt, uint32_t n)
	_(maintains \wrapped(stuffer))
	_(requires n==> \mutable((uint8_t[n]) outt))
    _(writes n ? {(uint8_t[n]) outt} : {})
	_(ensures n==> \wrapped((uint8_t[n]) outt))
	_(requires n <= s2n_stuffer_data_available(stuffer))
	//_(ensures \forall size_t i; i<n ==> outt[i] == stuffer->blob.val[i])
;

extern int s2n_stuffer_write_bytes(struct s2n_stuffer *stuffer, const uint8_t *in, const uint32_t n)
	_(maintains \wrapped(stuffer))
	_(maintains n==>\wrapped((uint8_t[n]) in))
    _(writes n ? {(uint8_t[n]) in} : {})
	_(requires s2n_stuffer_space_remaining(stuffer))
	_(writes stuffer)
	//_(ensures \forall size_t i; i<n ==> in[i] == stuffer->blob.val[i])
;

extern int s2n_stuffer_skip_read(struct s2n_stuffer *stuffer, uint32_t n)
	_(maintains \wrapped(stuffer))
	_(writes stuffer)
	_(requires n <= s2n_stuffer_data_available( stuffer ))
	_(ensures stuffer->read_cursor == \old(stuffer->read_cursor)+n)
;

extern int s2n_stuffer_skip_write(struct s2n_stuffer *stuffer, const uint32_t n)
	_(maintains \wrapped(stuffer))
	_(writes stuffer)
	_(requires n <= s2n_stuffer_space_remaining( stuffer ))
	_(ensures stuffer->write_cursor == \old(stuffer->write_cursor)+n)
;

/* Raw read/write move the cursor along and give you a pointer you can
 * read/write data_len bytes from/to in-place.
 */
extern void *s2n_stuffer_raw_write(struct s2n_stuffer *stuffer, const uint32_t data_len)
	_(writes \extent(stuffer))
	_(maintains \wrapped(stuffer))
	_(requires data_len<=s2n_stuffer_space_remaining(stuffer))
	_(ensures stuffer->tainted)
	_(ensures stuffer->write_cursor == \old(stuffer->write_cursor))
;

extern void *s2n_stuffer_raw_read(struct s2n_stuffer *stuffer, uint32_t data_len)
	_(writes stuffer)
	_(requires data_len <= s2n_stuffer_data_available( stuffer ))
	_(maintains \wrapped(stuffer))
	_(ensures stuffer->tainted)
	_(ensures stuffer->read_cursor == \old(stuffer->read_cursor))
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
extern int s2n_stuffer_copy(struct s2n_stuffer *from, struct s2n_stuffer *to, uint32_t len);

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
