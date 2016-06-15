#include <vcc.h>
#include <stdint.h>
#include "myblob.h"

extern int s2n_blob_init(struct s2n_blob *b, uint8_t *data, uint32_t size)
{
    b->data = data;
    b->size = size;
	b->allocated = size;
	b->user_allocated =1;
	b->mlocked = 0;
	wrap_blob(b);
    return 0;
}

extern int s2n_blob_zero(struct s2n_blob *b)
{
	_(unwrap b)
    if(b->size && b->data) memcpy(b->data,0,b->size);
	b->mlocked = 0;
	wrap_blob(b);
    return 0;
}
