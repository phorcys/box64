/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedlibsmTYPES_H_
#define __wrappedlibsmTYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef int64_t (*iFppp_t)(void*, void*, void*);
typedef int64_t (*iFpipp_t)(void*, int64_t, void*, void*);
typedef void* (*pFppiiLpppip_t)(void*, void*, int64_t, int64_t, uintptr_t, void*, void*, void*, int64_t, void*);

#define SUPER() ADDED_FUNCTIONS() \
	GO(SmcRequestSaveYourselfPhase2, iFppp_t) \
	GO(SmcInteractRequest, iFpipp_t) \
	GO(SmcOpenConnection, pFppiiLpppip_t)

#endif // __wrappedlibsmTYPES_H_
