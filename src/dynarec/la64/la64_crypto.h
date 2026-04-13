#ifndef __DYNAREC_LA64_CRYPTO_H__
#define __DYNAREC_LA64_CRYPTO_H__

#include <stdint.h>

typedef struct dynarec_la64_s dynarec_la64_t;

extern const uint8_t la64_vpaes_enc_tables[9][16];
extern const uint8_t la64_vpaes_dec_tables[9][16];
extern const uint8_t la64_vpaes_keygen_tables[8][16];
extern const uint8_t la64_vpaes_enc_tables_xv[9][32];
extern const uint8_t la64_vpaes_dec_tables_xv[9][32];

enum {
    LA64_VPAES_T0 = 16,
    LA64_VPAES_T1,
    LA64_VPAES_T2,
    LA64_VPAES_T3,
    LA64_VPAES_T4,
    LA64_VPAES_T5,
    LA64_VPAES_T6,
    LA64_VPAES_T7,
};

enum {
    LA64_VPAES_IPT_LO = 0,
    LA64_VPAES_IPT_HI,
    LA64_VPAES_INV_LO,
    LA64_VPAES_INV_HI,
    LA64_VPAES_SBO_LO,
    LA64_VPAES_SBO_HI,
    LA64_VPAES_SHIFTROWS,
};

enum {
    LA64_VPAES_DIPT_LO = 0,
    LA64_VPAES_DIPT_HI,
    LA64_VPAES_DINV_LO,
    LA64_VPAES_DINV_HI,
    LA64_VPAES_DSBO_LO,
    LA64_VPAES_DSBO_HI,
    LA64_VPAES_INVSHIFTROWS,
};

enum {
    LA64_VPAES_K_IPT_LO = 0,
    LA64_VPAES_K_IPT_HI,
    LA64_VPAES_K_INV_LO,
    LA64_VPAES_K_INV_HI,
    LA64_VPAES_K_SBO_LO,
    LA64_VPAES_K_SBO_HI,
    LA64_VPAES_K_SHUF,
    LA64_VPAES_K_RCON_MASK,
};

#ifdef LA64_VPAES_EMITTERS

static inline void la64_vpaes_load_tables_lsx(dynarec_la64_t* dyn, int ninst, int addr_reg, uintptr_t pool, int count)
{
    x87_purgecache(dyn, ninst, 0, x3, x4, x5);
    mmx_purgecache(dyn, ninst, 0, x5);
    TABLE64(addr_reg, pool);
    for (int i = 0; i < count; ++i)
        VLD(LA64_VPAES_T0 + i, addr_reg, i * 16);
}

static inline void la64_vpaes_load_tables_lasx(dynarec_la64_t* dyn, int ninst, int addr_reg, uintptr_t pool, int count)
{
    x87_purgecache(dyn, ninst, 0, x3, x4, x5);
    mmx_purgecache(dyn, ninst, 0, x5);
    TABLE64(addr_reg, pool);
    for (int i = 0; i < count; ++i)
        XVLD(LA64_VPAES_T0 + i, addr_reg, i * 32);
}

static inline void la64_vpaes_subbytes_lsx(dynarec_la64_t* dyn, int ninst, int dst, int zero, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    VXOR_V(zero, zero, zero);
    VANDI_B(t0, dst, 0x0f);
    VSRLI_B(t1, dst, 4);
    VSHUF_B(t2, zero, LA64_VPAES_T1, t1);
    VSHUF_B(dst, zero, LA64_VPAES_T0, t0);
    VXOR_V(dst, dst, t2);

    VANDI_B(t0, dst, 0x0f);
    VSHUF_B(t2, zero, LA64_VPAES_T3, t0);
    VSRLI_B(t1, dst, 4);
    VSHUF_B(dst, zero, LA64_VPAES_T2, t1);
    VXOR_V(t3, t1, t0);
    VXOR_V(dst, dst, t2);
    VSHUF_B(t0, zero, LA64_VPAES_T2, t3);
    VSHUF_B(dst, zero, LA64_VPAES_T2, dst);
    VXOR_V(t2, t0, t2);
    VXOR_V(t0, dst, t3);
    VSHUF_B(t2, zero, LA64_VPAES_T2, t2);
    VSHUF_B(t0, zero, LA64_VPAES_T4, t0);
    VXOR_V(t2, t2, t1);
    VSHUF_B(t2, zero, LA64_VPAES_T5, t2);
    VXOR_V(dst, t0, t2);
    VXORI_B(dst, dst, 99);
}

static inline void la64_vpaes_invsubbytes_lsx(dynarec_la64_t* dyn, int ninst, int dst, int zero, int t0, int t1, int t2, int t3, int t4)
{
    (void)dyn;
    (void)ninst;
    VXOR_V(zero, zero, zero);
    VXORI_B(dst, dst, 99);
    VANDI_B(t0, dst, 0x0f);
    VSRLI_B(t1, dst, 4);
    VSHUF_B(t1, zero, LA64_VPAES_T1, t1);
    VSHUF_B(dst, zero, LA64_VPAES_T0, t0);
    VXOR_V(dst, dst, t1);

    VANDI_B(t0, dst, 0x0f);
    VSRLI_B(t1, dst, 4);
    VSHUF_B(t2, zero, LA64_VPAES_T2, t1);
    VSHUF_B(t3, zero, LA64_VPAES_T3, t0);
    VXOR_V(t0, t1, t0);
    VXOR_V(t2, t2, t3);
    VSHUF_B(t4, zero, LA64_VPAES_T2, t0);
    VSHUF_B(t2, zero, LA64_VPAES_T2, t2);
    VXOR_V(t3, t4, t3);
    VXOR_V(t0, t2, t0);
    VSHUF_B(t3, zero, LA64_VPAES_T2, t3);
    VXOR_V(t3, t3, t1);
    VSHUF_B(t0, zero, LA64_VPAES_T4, t0);
    VSHUF_B(t1, zero, LA64_VPAES_T5, t3);
    VXOR_V(dst, t0, t1);
}

static inline void la64_vpaes_mixcolumns_lsx(dynarec_la64_t* dyn, int ninst, int dst, int poly, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    VSRLI_B(t0, dst, 7);
    VMUL_B(t0, t0, poly);
    VSHUF4I_B(t1, dst, 0x39);
    VSRLI_B(t2, t1, 7);
    VSHUF4I_B(t3, dst, 0x4e);
    VMUL_B(t2, t2, poly);
    VSLLI_B(dst, dst, 1);
    VXOR_V(dst, dst, t0);
    VSHUF4I_B(t0, t3, 0x39);
    VXOR_V(t3, t3, t0);
    VSLLI_B(t0, t1, 1);
    VXOR_V(t0, t0, t2);
    VXOR_V(t0, t0, t1);
    VXOR_V(dst, dst, t0);
    VXOR_V(dst, dst, t3);
}

static inline void la64_vpaes_xtime_table_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src, int tmp, int tab_lo, int tab_hi)
{
    (void)dyn;
    (void)ninst;
    VANDI_B(tmp, src, 0x0f);
    VSRLI_B(dst, src, 4);
    VSHUF_B(tmp, tab_lo, tab_lo, tmp);
    VSHUF_B(dst, tab_hi, tab_hi, dst);
    VXOR_V(dst, dst, tmp);
}

static inline void la64_vpaes_mixcolumns_xtime_lsx(dynarec_la64_t* dyn, int ninst, int dst, int tab_lo, int tab_hi, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    la64_vpaes_xtime_table_lsx(dyn, ninst, t0, dst, t3, tab_lo, tab_hi);
    VSHUF4I_B(t1, dst, 0x39);
    VSHUF4I_B(t2, dst, 0x4e);
    la64_vpaes_xtime_table_lsx(dyn, ninst, dst, t1, t3, tab_lo, tab_hi);
    VSHUF4I_B(t3, t2, 0x39);
    VXOR_V(t2, t2, t3);
    VXOR_V(dst, dst, t1);
    VXOR_V(dst, dst, t0);
    VXOR_V(dst, dst, t2);
}

static inline void la64_vpaes_invmixcolumns_lsx(dynarec_la64_t* dyn, int ninst, int dst, int poly, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    VSHUF4I_B(t0, dst, 0x4e);
    VXOR_V(t0, t0, dst);
    VSRLI_B(t1, t0, 7);
    VMUL_B(t1, t1, poly);
    VSLLI_B(t0, t0, 1);
    VXOR_V(t0, t0, t1);
    VSRLI_B(t1, t0, 7);
    VMUL_B(t1, t1, poly);
    VSLLI_B(t0, t0, 1);
    VXOR_V(t0, t0, t1);
    VXOR_V(dst, dst, t0);
    la64_vpaes_mixcolumns_lsx(dyn, ninst, dst, poly, t0, t1, t2, t3);
}

static inline void la64_vpaes_invmixcolumns_xtime_lsx(dynarec_la64_t* dyn, int ninst, int dst, int tab_lo, int tab_hi, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    VSHUF4I_B(t0, dst, 0x4e);
    VXOR_V(t0, t0, dst);
    la64_vpaes_xtime_table_lsx(dyn, ninst, t0, t0, t1, tab_lo, tab_hi);
    la64_vpaes_xtime_table_lsx(dyn, ninst, t0, t0, t1, tab_lo, tab_hi);
    VXOR_V(dst, dst, t0);
    la64_vpaes_mixcolumns_xtime_lsx(dyn, ninst, dst, tab_lo, tab_hi, t0, t1, t2, t3);
}

static inline void la64_vpaes_subbytes_lasx(dynarec_la64_t* dyn, int ninst, int dst, int zero, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    XVXOR_V(zero, zero, zero);
    XVANDI_B(t0, dst, 0x0f);
    XVSRLI_B(t1, dst, 4);
    XVSHUF_B(t2, zero, LA64_VPAES_T1, t1);
    XVSHUF_B(dst, zero, LA64_VPAES_T0, t0);
    XVXOR_V(dst, dst, t2);

    XVANDI_B(t0, dst, 0x0f);
    XVSHUF_B(t2, zero, LA64_VPAES_T3, t0);
    XVSRLI_B(t1, dst, 4);
    XVSHUF_B(dst, zero, LA64_VPAES_T2, t1);
    XVXOR_V(t3, t1, t0);
    XVXOR_V(dst, dst, t2);
    XVSHUF_B(t0, zero, LA64_VPAES_T2, t3);
    XVSHUF_B(dst, zero, LA64_VPAES_T2, dst);
    XVXOR_V(t2, t0, t2);
    XVXOR_V(t0, dst, t3);
    XVSHUF_B(t2, zero, LA64_VPAES_T2, t2);
    XVSHUF_B(t0, zero, LA64_VPAES_T4, t0);
    XVXOR_V(t2, t2, t1);
    XVSHUF_B(t2, zero, LA64_VPAES_T5, t2);
    XVXOR_V(dst, t0, t2);
    XVXORI_B(dst, dst, 99);
}

static inline void la64_vpaes_invsubbytes_lasx(dynarec_la64_t* dyn, int ninst, int dst, int zero, int t0, int t1, int t2, int t3, int t4)
{
    (void)dyn;
    (void)ninst;
    XVXOR_V(zero, zero, zero);
    XVXORI_B(dst, dst, 99);
    XVANDI_B(t0, dst, 0x0f);
    XVSRLI_B(t1, dst, 4);
    XVSHUF_B(t1, zero, LA64_VPAES_T1, t1);
    XVSHUF_B(dst, zero, LA64_VPAES_T0, t0);
    XVXOR_V(dst, dst, t1);

    XVANDI_B(t0, dst, 0x0f);
    XVSRLI_B(t1, dst, 4);
    XVSHUF_B(t2, zero, LA64_VPAES_T2, t1);
    XVSHUF_B(t3, zero, LA64_VPAES_T3, t0);
    XVXOR_V(t0, t1, t0);
    XVXOR_V(t2, t2, t3);
    XVSHUF_B(t4, zero, LA64_VPAES_T2, t0);
    XVSHUF_B(t2, zero, LA64_VPAES_T2, t2);
    XVXOR_V(t3, t4, t3);
    XVXOR_V(t0, t2, t0);
    XVSHUF_B(t3, zero, LA64_VPAES_T2, t3);
    XVXOR_V(t3, t3, t1);
    XVSHUF_B(t0, zero, LA64_VPAES_T4, t0);
    XVSHUF_B(t1, zero, LA64_VPAES_T5, t3);
    XVXOR_V(dst, t0, t1);
}

static inline void la64_vpaes_mixcolumns_lasx(dynarec_la64_t* dyn, int ninst, int dst, int poly, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    XVSRLI_B(t0, dst, 7);
    XVMUL_B(t0, t0, poly);
    XVSHUF4I_B(t1, dst, 0x39);
    XVSRLI_B(t2, t1, 7);
    XVSHUF4I_B(t3, dst, 0x4e);
    XVMUL_B(t2, t2, poly);
    XVSLLI_B(dst, dst, 1);
    XVXOR_V(dst, dst, t0);
    XVSHUF4I_B(t0, t3, 0x39);
    XVXOR_V(t3, t3, t0);
    XVSLLI_B(t0, t1, 1);
    XVXOR_V(t0, t0, t2);
    XVXOR_V(t0, t0, t1);
    XVXOR_V(dst, dst, t0);
    XVXOR_V(dst, dst, t3);
}

static inline void la64_vpaes_xtime_table_lasx(dynarec_la64_t* dyn, int ninst, int dst, int src, int tmp, int tab_lo, int tab_hi)
{
    (void)dyn;
    (void)ninst;
    XVANDI_B(tmp, src, 0x0f);
    XVSRLI_B(dst, src, 4);
    XVSHUF_B(tmp, tab_lo, tab_lo, tmp);
    XVSHUF_B(dst, tab_hi, tab_hi, dst);
    XVXOR_V(dst, dst, tmp);
}

static inline void la64_vpaes_mixcolumns_xtime_lasx(dynarec_la64_t* dyn, int ninst, int dst, int tab_lo, int tab_hi, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    la64_vpaes_xtime_table_lasx(dyn, ninst, t0, dst, t3, tab_lo, tab_hi);
    XVSHUF4I_B(t1, dst, 0x39);
    XVSHUF4I_B(t2, dst, 0x4e);
    la64_vpaes_xtime_table_lasx(dyn, ninst, dst, t1, t3, tab_lo, tab_hi);
    XVSHUF4I_B(t3, t2, 0x39);
    XVXOR_V(t2, t2, t3);
    XVXOR_V(dst, dst, t1);
    XVXOR_V(dst, dst, t0);
    XVXOR_V(dst, dst, t2);
}

static inline void la64_vpaes_invmixcolumns_lasx(dynarec_la64_t* dyn, int ninst, int dst, int poly, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    XVSHUF4I_B(t0, dst, 0x4e);
    XVXOR_V(t0, t0, dst);
    XVSRLI_B(t1, t0, 7);
    XVMUL_B(t1, t1, poly);
    XVSLLI_B(t0, t0, 1);
    XVXOR_V(t0, t0, t1);
    XVSRLI_B(t1, t0, 7);
    XVMUL_B(t1, t1, poly);
    XVSLLI_B(t0, t0, 1);
    XVXOR_V(t0, t0, t1);
    XVXOR_V(dst, dst, t0);
    la64_vpaes_mixcolumns_lasx(dyn, ninst, dst, poly, t0, t1, t2, t3);
}

static inline void la64_vpaes_invmixcolumns_xtime_lasx(dynarec_la64_t* dyn, int ninst, int dst, int tab_lo, int tab_hi, int t0, int t1, int t2, int t3)
{
    (void)dyn;
    (void)ninst;
    XVSHUF4I_B(t0, dst, 0x4e);
    XVXOR_V(t0, t0, dst);
    la64_vpaes_xtime_table_lasx(dyn, ninst, t0, t0, t1, tab_lo, tab_hi);
    la64_vpaes_xtime_table_lasx(dyn, ninst, t0, t0, t1, tab_lo, tab_hi);
    XVXOR_V(dst, dst, t0);
    la64_vpaes_mixcolumns_xtime_lasx(dyn, ninst, dst, tab_lo, tab_hi, t0, t1, t2, t3);
}

static inline void la64_vpaes_keygenassist_lsx(dynarec_la64_t* dyn, int ninst, int dst, int zero, int t0, int t1, int t2, int t3, int rcon, uint8_t imm)
{
    (void)dyn;
    (void)ninst;
    la64_vpaes_subbytes_lsx(dyn, ninst, dst, zero, t0, t1, t2, t3);
    VSHUF_B(dst, zero, dst, LA64_VPAES_T6);
    VLDI(rcon, ((0b000<<12)|imm));
    VAND_V(rcon, rcon, LA64_VPAES_T7);
    VXOR_V(dst, dst, rcon);
}

#endif

#endif
