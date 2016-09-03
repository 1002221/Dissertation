#include <vcc.h>
#include <stdint.h>

_(typedef _(record) struct Num {
    \natural len;
    uint8_t val[\natural];
} Num;) 

_(def \bool valid_num(Num n1)
{
    return (\forall \natural i; i >= n1.len ==> n1.val[i] == 0x0);
})

_(def Num xor(Num n1, Num n2)
    _(requires n1.len == n2.len)
    _(requires valid_num(n1) && valid_num(n2))
    _(ensures valid_num(\result))
{
    return n1 / {.val = (\lambda \natural i; (uint8_t)(i < n1.len ? n1.val[i] ^ n2.val[i] : 0))}; //spaces before relational operations
})

_(def Num make_num(uint8_t *a, size_t b)
    _(ensures valid_num(\result))
{
    Num n;
    return n / {.val = (\lambda \natural i; i<b ? a[i] : (uint8_t)0x0), .len = b};
})

/*given a value and a size, makes a usable num composed of that value repeated throughout the array range;*/
_(def Num repeat(uint8_t a, \natural size)
    _(ensures valid_num(\result))
{
    Num temp;
    return temp / {.val = (\lambda \natural i; i < size ? a : (uint8_t)0x0), .len = size};
})

/*takes two usable nums and places the second one after the first one to form a new usable num;*/
_(def Num concatenate(Num n1, Num n2)
    _(requires valid_num(n1) && valid_num(n2))
    _(ensures valid_num(\result))
{
    return n1 / {.val = (\lambda \natural i; i < n1.len ? n1.val[i] : (i < n1.len + n2.len ? n2.val[i-n1.len] : (uint8_t)0x0)), 
                 .len = n1.len + n2.len};
})

/*takes a usable num and removes everything in the num whose index is less than a given integer*/
_(def Num deconcatenate(\natural size, Num n2)
    _(requires valid_num(n2))
    _(requires n2.len >= size)
    _(ensures valid_num(\result))
{
    return n2 / {.val = (\lambda \natural i; i < n2.len - size ? n2.val[i + size] : (uint8_t)0x0), .len = n2.len - size};
})

/*replaces entries / appends zeros to resize a usable num, keeping it usable*/
_(ghost _(pure) \natural min(\natural a, \natural b) _(decreases 0){ if (a <= b) return a; else return b; })


_(def Num num_resize(Num n1, \natural size)
    _(ensures valid_num(\result))
{
    if(size <= n1.len)
    {
        return n1/{.val = (\lambda \natural i; i<size? n1.val[i] : (uint8_t)0x0), .len = size};
    }
    else
    {
        return n1/{.val = (\lambda \natural i; i<n1.len? n1.val[i] : (uint8_t)0x0), .len = size};
    }
})

_(def void xor_ass()
    _(ensures \forall uint8_t a, b, c; (uint8_t)(a^(b^c)) == (uint8_t)((a^b)^c))
{
    _(assert {:bv} \forall uint8_t a,b,c; _(unchecked)((_(unchecked)(a^b)^c))==_(unchecked)((a^_(unchecked)(b^c))))
})
