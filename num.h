#include <vcc.h>
#include <stdint.h>

_(typedef _(record) struct Num {
    \natural len;
    uint8_t val[\natural];
}Num;)

_(def Num xor(Num n1, Num n2)
_(requires n1.len == n2.len)
_(requires valid(n1) && valid(n2))
_(ensures valid(\result))
    {
        return n1 / {.val = (\lambda \natural i; (uint8_t)(i<n1.len? n1.val[i] ^ n2.val[i] : 0))};
    }
)

_(def \bool valid(Num n1)
{
    return (\forall \natural i; i>= n1.len ==> n1.val[i]==0);
})

_(def \bool xor_comm(Num n1, Num n2)
_(requires valid(n1) && valid(n2))
_(requires n1.len == n2.len && n2.len)
_(ensures \result == 1)
{
    return (xor(n1,n2) == xor(n2,n1));
}
)

_(def Num make_num(uint8_t *a, size_t b)
{
    Num n;
    return n/{.val = (\lambda \natural i; i<b? a[i] : (uint8_t)0), .len=0};
})

_(def Num repeat(uint8_t a, \natural size)
_(ensures valid(\result))
{
    Num temp;
    return temp / {.val = (\lambda \natural i; i<size? a : (uint8_t)0), .len = size} ;
})

_(def void xor_ass(Num n1, Num n2, Num n3)
_(requires valid(n1) && valid(n2) && valid(n3))
_(requires n1.len == n2.len && n2.len == n3.len)
_(ensures xor(xor(n1,n2),n3) == xor(n1,xor(n2,n3)))
{})

_(def void xor_idempotent(Num n1, uint8_t a)
_(requires valid(n1))
_(ensures xor(xor(n1,repeat(a,n1.len)),repeat(a,n1.len)) == n1)
{})

_(def Num concatenate(Num n1, Num n2)
_(requires valid(n1) && valid(n2))
_(ensures valid(\result))
{
    return n1 / {.val = (\lambda \natural i; i<n1.len? n1.val[i] : n2.val[i+n1.len]), .len = n1.len+n2.len};
})

_(def void concatenate_ass(Num n1, Num n2, Num n3)
_(requires valid(n1) && valid(n2) && valid(n3))
_(ensures concatenate(concatenate(n1,n2),n3) == concatenate(n1, concatenate(n2,n3)))
{})

_(def void xor_repeat_distrib(uint8_t a, uint8_t b, \natural n)
_(ensures xor(repeat(a,n),repeat(b,n)) == repeat((uint8_t)(a^b),n)){}
)

_(def void concatenate_distrib(Num n1, Num n2, Num n3, Num n4)
_(requires valid(n1) && valid(n2) && valid(n3) && valid(n4))
_(requires n1.len == n3.len && n2.len == n4.len)
_(ensures xor(concatenate(n1,n2),concatenate(n3,n4)) == concatenate(xor(n1,n3),xor(n2,n4)))
{})

_(def void xor_def(uint8_t a, uint8_t b)
_(ensures a^b == (a + b)%2)
{})

_(def Num num_resize(Num n1, \natural size)
_(maintains valid(n1))
{
    if(size < n1.len)
    {
        return n1/{.val = (\lambda \natural i; i<size? n1.val[i] : (uint8_t)0), .len = size};
    }
    else if(size == n1.len)
    {
        return n1;
    }
    else
    {
        return n1/{.val = (\lambda \natural i; i<n1.len? n1.val[i] : (uint8_t)0), .len = size};
    }
})

_(def Num num_segment(Num n1, \natural rear, \natural front, uint8_t a)
_(maintains valid(n1))
{
    return n1/{.val = (\lambda \natural i; i>=rear && i< front? a : n1.val[i])};
})

_(def void xor_combine(uint8_t a, uint8_t b, Num n)
_(ensures xor(xor(n,repeat(a,n.len)),repeat(b,n.len)) == xor(n,repeat((uint8_t)(a^b),n.len)))
{})
