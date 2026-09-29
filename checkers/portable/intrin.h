/* Portable stand-ins for the four MSVC-specific functions used by cchk.c, for building it
   with gcc or clang (Linux, macOS) without changing cchk.c:
       gcc -O2 -fopenmp -I portable cchk.c -o cchk
   With a compiler that has no OpenMP (for example zig cc), add -I portable/noomp and
   drop -fopenmp; the checker then runs on one thread. */
#ifndef CCHK_PORTABLE_INTRIN_H
#define CCHK_PORTABLE_INTRIN_H
#include <stdint.h>
#include <stdlib.h>
/* NOLINTBEGIN(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp): the MSVC names are the point */
__extension__ typedef __int128 cchk_int128;
__extension__ typedef unsigned __int128 cchk_uint128;
static inline int64_t _mul128(int64_t a, int64_t b, int64_t *hi)
{
    cchk_int128 p = (cchk_int128)a * b;
    *hi = (int64_t)(p >> 64);
    return (int64_t)(uint64_t)p;
}
static inline uint64_t _umul128(uint64_t a, uint64_t b, uint64_t *hi)
{
    cchk_uint128 p = (cchk_uint128)a * b;
    *hi = (uint64_t)(p >> 64);
    return (uint64_t)p;
}
static inline unsigned char cchk_addcarry_u64(unsigned char c, uint64_t a, uint64_t b, uint64_t *out)
{
    cchk_uint128 s = (cchk_uint128)a + b + c;
    *out = (uint64_t)s;
    return (unsigned char)(s >> 64);
}
#define _addcarry_u64 cchk_addcarry_u64
#define _strtoi64 strtoll
/* NOLINTEND(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
#endif
