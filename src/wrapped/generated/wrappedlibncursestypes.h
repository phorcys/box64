/*******************************************************************
 * File automatically generated by rebuild_wrappers.py (v2.1.0.16) *
 *******************************************************************/
#ifndef __wrappedlibncursesTYPES_H_
#define __wrappedlibncursesTYPES_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef void* (*pFv_t)(void);
typedef int64_t (*iFpV_t)(void*, ...);
typedef int64_t (*iFppA_t)(void*, void*, va_list);
typedef int64_t (*iFiipV_t)(int64_t, int64_t, void*, ...);
typedef int64_t (*iFpiipV_t)(void*, int64_t, int64_t, void*, ...);

#define SUPER() ADDED_FUNCTIONS() \
	GO(initscr, pFv_t) \
	GO(printw, iFpV_t) \
	GO(vwprintw, iFppA_t) \
	GO(mvprintw, iFiipV_t) \
	GO(mvwprintw, iFpiipV_t)

#endif // __wrappedlibncursesTYPES_H_
