/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedsdl2ttfTYPES_H_
#define __wrappedsdl2ttfTYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef void* (*pFpii_t)(void*, int64_t, int64_t);
typedef void* (*pFpiii_t)(void*, int64_t, int64_t, int64_t);

#define SUPER() ADDED_FUNCTIONS() \
	GO(TTF_OpenFontRW, pFpii_t) \
	GO(TTF_OpenFontIndexRW, pFpiii_t)

#endif // __wrappedsdl2ttfTYPES_H_
