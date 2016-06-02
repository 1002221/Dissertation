#include <vcc.h>
//#include "myerrno.h"
#include <stdint.h>
//#include "mysafety.h"
#include "myblob.h"

//#include "mys2n.h"

extern int s2n_blob_init(struct s2n_blob *b, uint8_t *data, uint32_t size)
{
    b->data = data;
    b->size = size;
	b->allocated = size;
	b->user_allocated =1;
	b->mlocked = 0;
	_(ghost { 
       b->val = \lambda size_t i; b->data[i];
       b->\owns = b->allocated ? {blob_data(b)} : {}; 
	   _(wrap b)
})
    return 0;
}

extern int s2n_blob_zero(struct s2n_blob *b)
{
    if(b->size && b->data) memcpy(b->data,0,b->size)
	b->user_allocated =1;
	b->mlocked = 0;
	_(ghost { 
       b->val = \lambda size_t i; b->data[i];
       b->\owns = b->allocated ? {blob_data(b)} : {}; 
	   _(wrap b)
})
    return 0;
}
