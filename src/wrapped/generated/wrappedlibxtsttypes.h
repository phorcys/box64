/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedlibxtstTYPES_H_
#define __wrappedlibxtstTYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef int64_t (*iFpppp_t)(void*, void*, void*, void*);

#define SUPER() ADDED_FUNCTIONS() \
	GO(XRecordEnableContext, iFpppp_t) \
	GO(XRecordEnableContextAsync, iFpppp_t)

#endif // __wrappedlibxtstTYPES_H_
