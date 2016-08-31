#include <vcc.h>
#include <stdint.h>

_(typedef _(record) struct Num {
    \natural len;
    uint8_t val[\natural];
}Num;)

_(def Num xor(Num n1, Num n2)
    _(requires n1.len == n2.len)
    _(requires usable_num(n1) && usable_num(n2))
    _(ensures usable_num(\result))
{
    return n1 / {.val = (\lambda \natural i; (uint8_t)(i<n1.len? n1.val[i] ^ n2.val[i] : 0))};
}
)

_(def \bool usable_num(Num n1)
{
    return (\forall \natural i; i>= n1.len ==> n1.val[i]==0x0);
})

_(def Num make_num(uint8_t *a, size_t b)
    _(ensures usable_num(\result))
{
    Num n;
    return n/{.val = (\lambda \natural i; i<b? a[i] : (uint8_t)0x0), .len=b};
})

_(def Num repeat(uint8_t a, \natural size)
    _(ensures usable_num(\result))
{
    Num temp;
    return temp / {.val = (\lambda \natural i; i<size? a : (uint8_t)0x0), .len = size} ;
})

_(def Num concatenate(Num n1, Num n2)
    _(requires usable_num(n1) && usable_num(n2))
    _(ensures usable_num(\result))
{
    return n1 / {.val = (\lambda \natural i; i<n1.len? n1.val[i] : (i<n1.len+n2.len? n2.val[i-n1.len] : (uint8_t)0x0)), .len = n1.len+n2.len};
})

_(def Num deconcatenate(\natural size, Num n2)
    _(requires usable_num(n2))
    _(requires n2.len >= size)
    _(ensures usable_num(\result))
{
    return n2 / {.val = (\lambda \natural i; i<n2.len-size? n2.val[i+size] : (uint8_t)0x0), .len = n2.len-size};
})

_(def Num num_resize(Num n1, \natural size)
    _(ensures usable_num(\result))
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
    _(ensures \forall uint8_t a,b,c; (uint8_t)(a^(b^c)) == (uint8_t)((a^b)^c))
{
    _(assert {:bv} \forall uint8_t a,b,c; _(unchecked)((_(unchecked)(a^b)^c))==_(unchecked)((a^_(unchecked)(b^c))))
})
