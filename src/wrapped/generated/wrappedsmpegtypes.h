/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedsmpegTYPES_H_
#define __wrappedsmpegTYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef void* (*pFppi_t)(void*, void*, int64_t);
typedef void (*vFpppp_t)(void*, void*, void*, void*);

#define SUPER() ADDED_FUNCTIONS() \
	GO(SMPEG_new_rwops, pFppi_t) \
	GO(SMPEG_setdisplay, vFpppp_t)

#endif // __wrappedsmpegTYPES_H_
