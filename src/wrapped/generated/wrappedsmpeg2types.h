/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedsmpeg2TYPES_H_
#define __wrappedsmpeg2TYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef void (*vFpppp_t)(void*, void*, void*, void*);
typedef void* (*pFppii_t)(void*, void*, int64_t, int64_t);

#define SUPER() ADDED_FUNCTIONS() \
	GO(SMPEG_setdisplay, vFpppp_t) \
	GO(SMPEG_new_rwops, pFppii_t)

#endif // __wrappedsmpeg2TYPES_H_
