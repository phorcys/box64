#ifndef __DYNAREC_LA64_CRYPTO_H__
#define __DYNAREC_LA64_CRYPTO_H__

#include <stdint.h>

typedef struct dynarec_la64_s dynarec_la64_t;
typedef struct x64emu_s x64emu_t;

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

// Uses x1-x7 scratch GPRs only, so it can be expanded multiple times in one opcode path.
#define LA64_PCLMUL64_CTZ_GPR(LHS, RHS, SHIFT, RES_LO, RES_HI, TMP_LO, TMP_HI) \
    do {                                                                         \
        XOR((RES_LO), (RES_LO), (RES_LO));                                       \
        XOR((RES_HI), (RES_HI), (RES_HI));                                       \
        /* Skip the 12-instruction loop body when lhs is zero. */                \
        BEQZ((LHS), 52);                                                         \
        CTZ_D((SHIFT), (LHS));                                                   \
        ADDI_D((TMP_HI), (LHS), -1);                                             \
        AND((LHS), (LHS), (TMP_HI));                                             \
        SLL_D((TMP_LO), (RHS), (SHIFT));                                         \
        ADDI_D((TMP_HI), xZR, 64);                                               \
        SUB_D((TMP_HI), (TMP_HI), (SHIFT));                                      \
        SRL_D((TMP_HI), (RHS), (TMP_HI));                                        \
        SNEZ((SHIFT), (SHIFT));                                                  \
        NEG_D((SHIFT), (SHIFT));                                                 \
        AND((TMP_HI), (TMP_HI), (SHIFT));                                        \
        XOR((RES_LO), (RES_LO), (TMP_LO));                                       \
        XOR((RES_HI), (RES_HI), (TMP_HI));                                       \
        BNEZ((LHS), -48);                                                        \
    } while (0)

#define LA64_PCLMUL128_PACK_LSX(DST, LO, HI) \
    do {                                     \
        VXOR_V((DST), (DST), (DST));         \
        VINSGR2VR_D((DST), (LO), 0);         \
        VINSGR2VR_D((DST), (HI), 1);         \
    } while (0)

#define LA64_SHAEXT_PACK4_W(DST, W0, W1, W2, W3) \
    do {                                         \
        VXOR_V((DST), (DST), (DST));             \
        VINSGR2VR_W((DST), (W0), 0);             \
        VINSGR2VR_W((DST), (W1), 1);             \
        VINSGR2VR_W((DST), (W2), 2);             \
        VINSGR2VR_W((DST), (W3), 3);             \
    } while (0)

#define LA64_SHAEXT_MAJ(DST, A, B, C, TMP) \
    do {                                   \
        OR((DST), (A), (B));               \
        AND((DST), (DST), (C));            \
        AND((TMP), (A), (B));              \
        OR((DST), (DST), (TMP));           \
    } while (0)

#define LA64_SHAEXT_SIGMA0(DST, SRC, T0, T1) \
    do {                                     \
        ROTRI_W((DST), (SRC), 2);            \
        ROTRI_W((T0), (SRC), 13);            \
        XOR((DST), (DST), (T0));             \
        ROTRI_W((T1), (SRC), 22);            \
        XOR((DST), (DST), (T1));             \
    } while (0)

#define LA64_SHAEXT_SIGMA1(DST, SRC, T0, T1) \
    do {                                     \
        ROTRI_W((DST), (SRC), 6);            \
        ROTRI_W((T0), (SRC), 11);            \
        XOR((DST), (DST), (T0));             \
        ROTRI_W((T1), (SRC), 25);            \
        XOR((DST), (DST), (T1));             \
    } while (0)

#define LA64_SHAEXT_ROR_W_LSX(DST, SRC, IMM, TMP) \
    do {                                          \
        (void)(TMP);                              \
        VROTRI_W((DST), (SRC), (IMM));            \
    } while (0)

#define LA64_SHAEXT_THO0_VEC_LSX(DST, SRC, TMP0, TMP1) \
    do {                                               \
        LA64_SHAEXT_ROR_W_LSX((DST), (SRC), 7, (TMP0));\
        LA64_SHAEXT_ROR_W_LSX((TMP1), (SRC), 18, (TMP0)); \
        VXOR_V((DST), (DST), (TMP1));                  \
        VSRLI_W((TMP1), (SRC), 3);                     \
        VXOR_V((DST), (DST), (TMP1));                  \
    } while (0)

#define LA64_SHAEXT_THO1_VEC_LSX(DST, SRC, TMP0, TMP1) \
    do {                                               \
        LA64_SHAEXT_ROR_W_LSX((DST), (SRC), 17, (TMP0)); \
        LA64_SHAEXT_ROR_W_LSX((TMP1), (SRC), 19, (TMP0)); \
        VXOR_V((DST), (DST), (TMP1));                  \
        VSRLI_W((TMP1), (SRC), 10);                    \
        VXOR_V((DST), (DST), (TMP1));                  \
    } while (0)

static inline void la64_sha1nexte_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src)
{
    int t0;
    t0 = fpu_get_scratch(dyn);
    (void)dyn;
    (void)ninst;
    VROTRI_W(t0, dst, 2);
    VADD_W(t0, t0, src);
    VOR_V(dst, src, src);
    VEXTRINS_W(dst, t0, VEXTRINS_IMM_4_0(3, 3));
}

static inline void la64_sha1msg1_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src)
{
    int t0;
    (void)ninst;
    t0 = fpu_get_scratch(dyn);
    VOR_V(t0, dst, dst);
    VPERMI_W(t0, src, 0x4e);             // [w5,w4,w3,w2] in lane order
    VXOR_V(dst, dst, t0);
}

static inline void la64_sha1msg2_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src)
{
    int t0, t1;
    (void)ninst;
    t0 = fpu_get_scratch(dyn);
    t1 = fpu_get_scratch(dyn);
    VBSLL_V(t0, src, 4);
    VXOR_V(t0, t0, dst);
    VROTRI_W(t1, t0, 31);
    VBSRL_V(t0, t1, 12);                 // lane0 = w16
    VXOR_V(t0, t0, dst);                 // lane0 = w15 ^ w16
    VROTRI_W(t0, t0, 31);                // lane0 = w19, other lanes are don't-care
    VOR_V(dst, t1, t1);
    VEXTRINS_W(dst, t0, VEXTRINS_IMM_4_0(0, 0));
}

static inline void la64_sha256msg1_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src)
{
    int t0, t1, t2, t3;
    (void)ninst;
    t0 = fpu_get_scratch(dyn);
    t1 = fpu_get_scratch(dyn);
    t2 = fpu_get_scratch(dyn);
    t3 = fpu_get_scratch(dyn);
    VBSRL_V(t0, dst, 4);
    VEXTRINS_W(t0, src, VEXTRINS_IMM_4_0(3, 0));
    LA64_SHAEXT_THO0_VEC_LSX(t1, t0, t2, t3);
    VADD_W(dst, dst, t1);
}

static inline void la64_sha256msg2_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src)
{
    int t0, t1, t2, t3;
    (void)ninst;
    t0 = fpu_get_scratch(dyn);
    t1 = fpu_get_scratch(dyn);
    t2 = fpu_get_scratch(dyn);
    t3 = fpu_get_scratch(dyn);
    VBSRL_V(t0, src, 8);
    LA64_SHAEXT_THO1_VEC_LSX(t1, t0, t2, t3);
    VADD_W(dst, dst, t1);
    VBSLL_V(t0, dst, 8);
    LA64_SHAEXT_THO1_VEC_LSX(t1, t0, t2, t3);
    VADD_W(dst, dst, t1);
}

static inline void la64_sha1rnds4_lsx(dynarec_la64_t* dyn, int ninst, int dst, int src, uint8_t ib)
{
    static const uint32_t ks[4] = {0x5A827999u, 0x6ED9EBA1u, 0x8F1BBCDCu, 0xCA62C1D6u};
    int t0, t1, t2;
    int mode = ib & 3;
    (void)ninst;
    t0 = fpu_get_scratch(dyn);
    t1 = fpu_get_scratch(dyn);
    t2 = fpu_get_scratch(dyn);
    VPICKVE2GR_WU(x1, dst, 3);
    VPICKVE2GR_WU(x2, dst, 2);
    VPICKVE2GR_WU(x3, dst, 1);
    VPICKVE2GR_WU(x4, dst, 0);
    switch (mode) {
        case 0:
            MOV32w(x5, ks[0]);
            VROTRI_W(t0, dst, 2);
            VXOR_V(t1, t1, t1);
            VPERMI_W(t1, dst, 0x04);     // [d, c, 0, 0]
            VEXTRINS_W(t1, t1, VEXTRINS_IMM_4_0(2, 0));
            VEXTRINS_W(t1, t0, VEXTRINS_IMM_4_0(0, 2));   // [rol30(b), c, d, 0]
            VREPLGR2VR_W(t2, x5);
            VADD_W(t1, t1, src);
            VADD_W(t1, t1, t2);          // lane3..0 = [w3+k, d+w2+k, c+w1+k, rol30(b)+w0+k]

            // Round 0: A=x1 B=x2 C=x3 D=x4
            ROTRI_W(x6, x1, 27);
            VPICKVE2GR_WU(x7, t1, 3);
            ADD_W(x6, x6, x7);
            AND(x7, x2, x3);
            ANDN(x4, x4, x2);            // D is dead after round 0
            XOR(x7, x7, x4);
            ADD_W(x6, x6, x7);
            ROTRI_W(x2, x2, 2);          // C1

            // Round 1: A=x6 B=x1 C=x2 D=x3
            ROTRI_W(x4, x6, 27);
            VPICKVE2GR_WU(x7, t1, 2);
            ADD_W(x4, x4, x7);
            AND(x7, x1, x2);
            ANDN(x3, x3, x1);            // D is dead after round 1
            XOR(x7, x7, x3);
            ADD_W(x4, x4, x7);
            ROTRI_W(x1, x1, 2);          // C2

            // Round 2: A=x4 B=x6 C=x1 D=x2
            ROTRI_W(x3, x4, 27);
            VPICKVE2GR_WU(x7, t1, 1);
            ADD_W(x3, x3, x7);
            AND(x7, x6, x1);
            ANDN(x2, x2, x6);            // D is dead after round 2
            XOR(x7, x7, x2);
            ADD_W(x3, x3, x7);
            ROTRI_W(x6, x6, 2);          // C3

            // Round 3: A=x3 B=x4 C=x6 D=x1
            ROTRI_W(x5, x3, 27);
            VPICKVE2GR_WU(x7, t1, 0);
            ADD_W(x5, x5, x7);
            AND(x7, x4, x6);
            ANDN(x1, x1, x4);            // D is dead after round 3
            XOR(x7, x7, x1);
            ADD_W(x5, x5, x7);
            ROTRI_W(x4, x4, 2);          // C4
            LA64_SHAEXT_PACK4_W(dst, x6, x4, x3, x5);
            break;
        case 1:
        case 3:
            MOV32w(x6, ks[mode]);
            VROTRI_W(t0, dst, 2);
            VXOR_V(t1, t1, t1);
            VPERMI_W(t1, dst, 0x04);
            VEXTRINS_W(t1, t1, VEXTRINS_IMM_4_0(2, 0));
            VEXTRINS_W(t1, t0, VEXTRINS_IMM_4_0(0, 2));
            VREPLGR2VR_W(t2, x6);
            VADD_W(t1, t1, src);
            VADD_W(t1, t1, t2);

            ROTRI_W(x5, x1, 27);
            VPICKVE2GR_WU(x7, t1, 3);
            ADD_W(x5, x5, x7);
            XOR(x7, x2, x3);
            XOR(x7, x7, x4);
            ADD_W(x5, x5, x7);
            ROTRI_W(x2, x2, 2);

            ROTRI_W(x4, x5, 27);
            VPICKVE2GR_WU(x7, t1, 2);
            ADD_W(x4, x4, x7);
            XOR(x7, x1, x2);
            XOR(x7, x7, x3);
            ADD_W(x4, x4, x7);
            ROTRI_W(x1, x1, 2);

            ROTRI_W(x3, x4, 27);
            VPICKVE2GR_WU(x7, t1, 1);
            ADD_W(x3, x3, x7);
            XOR(x7, x5, x1);
            XOR(x7, x7, x2);
            ADD_W(x3, x3, x7);
            ROTRI_W(x5, x5, 2);

            ROTRI_W(x6, x3, 27);
            VPICKVE2GR_WU(x7, t1, 0);
            ADD_W(x6, x6, x7);
            XOR(x7, x4, x5);
            XOR(x7, x7, x1);
            ADD_W(x6, x6, x7);
            ROTRI_W(x4, x4, 2);
            LA64_SHAEXT_PACK4_W(dst, x5, x4, x3, x6);
            break;
        default:
            MOV32w(x5, ks[2]);
            VROTRI_W(t0, dst, 2);
            VXOR_V(t1, t1, t1);
            VPERMI_W(t1, dst, 0x04);
            VEXTRINS_W(t1, t1, VEXTRINS_IMM_4_0(2, 0));
            VEXTRINS_W(t1, t0, VEXTRINS_IMM_4_0(0, 2));
            VREPLGR2VR_W(t2, x5);
            VADD_W(t1, t1, src);
            VADD_W(t1, t1, t2);

            ROTRI_W(x6, x1, 27);
            VPICKVE2GR_WU(x7, t1, 3);
            ADD_W(x6, x6, x7);
            XOR(x7, x2, x3);
            AND(x4, x4, x7);             // D is dead after round 0
            AND(x7, x2, x3);
            XOR(x7, x7, x4);
            ADD_W(x6, x6, x7);
            ROTRI_W(x2, x2, 2);

            ROTRI_W(x4, x6, 27);
            VPICKVE2GR_WU(x7, t1, 2);
            ADD_W(x4, x4, x7);
            XOR(x7, x1, x2);
            AND(x3, x3, x7);             // D is dead after round 1
            AND(x7, x1, x2);
            XOR(x7, x7, x3);
            ADD_W(x4, x4, x7);
            ROTRI_W(x1, x1, 2);

            ROTRI_W(x3, x4, 27);
            VPICKVE2GR_WU(x7, t1, 1);
            ADD_W(x3, x3, x7);
            XOR(x7, x6, x1);
            AND(x2, x2, x7);             // D is dead after round 2
            AND(x7, x6, x1);
            XOR(x7, x7, x2);
            ADD_W(x3, x3, x7);
            ROTRI_W(x6, x6, 2);

            ROTRI_W(x5, x3, 27);
            VPICKVE2GR_WU(x7, t1, 0);
            ADD_W(x5, x5, x7);
            XOR(x7, x4, x6);
            AND(x1, x1, x7);             // D is dead after round 3
            AND(x7, x4, x6);
            XOR(x7, x7, x1);
            ADD_W(x5, x5, x7);
            ROTRI_W(x4, x4, 2);
            LA64_SHAEXT_PACK4_W(dst, x6, x4, x3, x5);
            break;
    }
}

static inline void la64_sha256rnds2_lsx_mem_fallback(dynarec_la64_t* dyn, int ninst, int dst, int src, int xmm0, int vt0, int vt2)
{
    (void)dyn;
    (void)ninst;
    // Raw x86 layout:
    // src = [f, e, b, a]
    // dst = [h, g, d, c]
    VPICKVE2GR_WU(x1, src, 3);           // a0
    VPICKVE2GR_WU(x2, src, 2);           // b0
    VPICKVE2GR_WU(x3, dst, 3);           // c0
    LA64_SHAEXT_SIGMA0(x5, x1, x6, x6); // sigma0(a0)
    LA64_SHAEXT_MAJ(x7, x1, x2, x3, x6);// maj(a0,b0,c0)
    ADD_W(x7, x7, x5);                   // maj + sigma0

    // Round 1 T1 on the raw x86 layout.
    VSHUF4I_W(vt0, src, 0x00);           // ffff
    VBITSEL_V(vt0, dst, vt0, src);       // lane1 = ch(e0,f0,g0)

    VPICKVE2GR_WU(x4, src, 1);           // e0
    VADD_W(vt2, xmm0, dst);              // lane0 = msg0+h0, lane1 = msg1+h1
    LA64_SHAEXT_SIGMA1(x6, x4, x5, x5); // sigma1(e0)
    VSHUF4I_W(vt0, vt0, 0x55);           // broadcast ch0 from lane1
    VADD_W(vt0, vt0, vt2);               // lane0 = ch0 + msg0+h0
    VPICKVE2GR_WU(x5, vt0, 0);           // ch0 + msg0+h0
    ADD_W(x6, x6, x5);                   // t1_0

    VPICKVE2GR_WU(x5, dst, 2);           // d0

    ADD_W(x7, x7, x6);                   // new a1
    ADD_W(x5, x5, x6);                   // new e1

    // Start building the final x86-layout result early:
    // dst = [f2, e2, b2, a2], with f2=e1 and b2=a1 already known here.
    VINSGR2VR_W(dst, x5, 0);             // f2 = e1
    VINSGR2VR_W(dst, x7, 2);             // b2 = a1

    LA64_SHAEXT_SIGMA1(x4, x5, x6, x6); // sigma1(e1), started as early as possible

    // Round 2 reuses the scalar state from round 1:
    // dst.lane0 already holds e1, while src.lane1/src.lane0 hold f1/g1.
    VSHUF4I_W(vt0, src, 0x55);           // e0 broadcast = f1
    VBITSEL_V(vt0, src, vt0, dst);       // lane0 = ch(e1,e0,f0) = ch(e1,f1,g1)
    // a1 = x7, b1 = a0(x1), c1 = b0(x2), d1 = c0(x3).
    LA64_SHAEXT_SIGMA0(x6, x7, x5, x5); // sigma0(a1)
    LA64_SHAEXT_MAJ(x5, x7, x1, x2, x7);// maj(a1,b1,c1), x7 can be clobbered now
    ADD_W(x6, x6, x5);                   // maj + sigma0

    VPICKVE2GR_WU(x5, vt2, 1);           // msg1+h1
    VPICKVE2GR_WU(x7, vt0, 0);           // ch(e1,f1,g1)
    ADD_W(x6, x6, x5);                   // t2_partial + msg1+h1
    ADD_W(x3, x3, x5);                   // c0 + msg1+h1
    ADD_W(x4, x4, x7);                   // sigma1 + ch1
    ADD_W(x6, x6, x4);                   // new a2
    ADD_W(x4, x3, x4);                   // new e2

    VINSGR2VR_W(dst, x4, 1);             // e2
    VINSGR2VR_W(dst, x6, 3);             // a2
}

static inline void la64_sha256rnds2_lsx_pure7_scratch(dynarec_la64_t* dyn, int ninst, int dst, int src, int xmm0,
                                                      int vt0, int vt1, int vt2, int vt3, int vt4, int vt5, int vt6)
{
    (void)dyn;
    (void)ninst;
    // Full 7-scratch vector path for MODREG or non-aliasing memory cases.
    VADD_W(vt0, xmm0, dst);              // msg_h = [wk0+h0, wk1+g0, ...]
    VSHUF4I_W(vt1, src, 0xaa);           // b0
    VSHUF4I_W(vt2, src, 0x00);           // f0

    VROTRI_W(vt3, src, 2);
    VROTRI_W(vt6, src, 13);
    VXOR_V(vt3, vt3, vt6);
    VROTRI_W(vt6, src, 22);
    VXOR_V(vt3, vt3, vt6);               // lane3 = sigma0(a0)

    VROTRI_W(vt4, src, 6);
    VROTRI_W(vt6, src, 11);
    VXOR_V(vt4, vt4, vt6);
    VROTRI_W(vt6, src, 25);
    VXOR_V(vt4, vt4, vt6);               // lane1 = sigma1(e0)

    VBITSEL_V(vt5, dst, vt2, src);       // lane1 = ch(e0,f0,g0)
    VSHUF4I_W(vt6, vt0, 0x00);           // msg0+h0
    VADD_W(vt4, vt4, vt5);
    VADD_W(vt4, vt4, vt6);
    VSHUF4I_W(vt4, vt4, 0x55);           // t1_0 broadcast

    VOR_V(vt5, src, vt1);
    VAND_V(vt5, vt5, dst);
    VAND_V(vt6, src, vt1);
    VOR_V(vt5, vt5, vt6);                // lane3 = maj(a0,b0,c0)
    VADD_W(vt3, vt3, vt5);
    VADD_W(vt3, vt3, vt4);
    VSHUF4I_W(vt3, vt3, 0xff);           // a1 broadcast

    VSHUF4I_W(vt5, dst, 0xaa);           // d0
    VADD_W(vt5, vt5, vt4);               // e1
    VSHUF4I_W(dst, dst, 0xff);           // c0 kept

    VSHUF4I_W(vt6, src, 0x55);           // e0
    VBITSEL_V(vt4, vt2, vt6, vt5);       // ch(e1,e0,f0)
    VROTRI_W(vt6, vt5, 6);
    VROTRI_W(xmm0, vt5, 11);
    VXOR_V(vt6, vt6, xmm0);
    VROTRI_W(xmm0, vt5, 25);
    VXOR_V(vt6, vt6, xmm0);              // sigma1(e1)
    VADD_W(vt4, vt4, vt6);
    VSHUF4I_W(vt6, vt0, 0x55);           // msg1+h1
    VADD_W(vt4, vt4, vt6);               // t1_1
    VADD_W(dst, dst, vt4);               // e2 early

    VSHUF4I_W(vt2, src, 0xff);           // a0
    VROTRI_W(vt6, vt3, 2);
    VROTRI_W(xmm0, vt3, 13);
    VXOR_V(vt6, vt6, xmm0);
    VROTRI_W(xmm0, vt3, 22);
    VXOR_V(vt6, vt6, xmm0);              // sigma0(a1)
    VAND_V(xmm0, vt3, vt2);
    VAND_V(vt0, vt3, vt1);
    VXOR_V(xmm0, xmm0, vt0);
    VAND_V(vt0, vt2, vt1);
    VXOR_V(xmm0, xmm0, vt0);             // maj(a1,a0,b0)
    VADD_W(vt6, vt6, xmm0);
    VADD_W(vt6, vt6, vt4);               // a2

    VILVL_W(vt0, dst, vt5);
    VILVL_W(vt2, vt6, vt3);
    VPICKEV_D(dst, vt2, vt0);
}

static inline void la64_sha256rnds2_lsx_pure6_modreg(dynarec_la64_t* dyn, int ninst, int dst, int src, int xmm0,
                                                     int vt0, int vt1, int vt2, int vt3, int vt4, int vt5)
{
    (void)dyn;
    (void)ninst;
    // 6-scratch MODREG-only path used for the gd==xmm0 alias case.
    // Uses dst and xmm0 as working vector registers.
    // Preconditions for this helper:
    // - explicit source is MODREG (no mem scratch pressure)
    // - xmm0 has been copied to a scratch register, so it can be clobbered

    VADD_W(vt0, xmm0, dst);              // msg_h = [wk0+h0, wk1+g0, ...]

    // round 1 t2 = sigma0(a0) + maj(a0,b0,c0)
    VSHUF4I_W(vt1, src, 0xff);           // a0
    VROTRI_W(vt3, vt1, 2);
    VROTRI_W(vt5, vt1, 13);
    VXOR_V(vt3, vt3, vt5);
    VROTRI_W(vt5, vt1, 22);
    VXOR_V(vt3, vt3, vt5);               // sigma0(a0)

    VSHUF4I_W(vt4, src, 0xff);           // a0
    VSHUF4I_W(vt5, src, 0xaa);           // b0
    VAND_V(vt4, vt4, vt5);               // a0 & b0
    VSHUF4I_W(vt2, dst, 0xff);           // c0
    VSHUF4I_W(vt5, src, 0xff);           // a0
    VAND_V(vt2, vt2, vt5);               // a0 & c0
    VXOR_V(vt4, vt4, vt2);
    VSHUF4I_W(vt2, src, 0xaa);           // b0
    VSHUF4I_W(vt5, dst, 0xff);           // c0
    VAND_V(vt2, vt2, vt5);               // b0 & c0
    VXOR_V(vt4, vt4, vt2);               // maj(a0,b0,c0)
    VADD_W(vt4, vt4, vt3);               // t2_0

    // round 1 t1 = sigma1(e0) + ch(e0,f0,g0) + msg0+h0
    VSHUF4I_W(vt2, src, 0x55);           // e0
    VROTRI_W(vt3, vt2, 6);
    VROTRI_W(vt5, vt2, 11);
    VXOR_V(vt3, vt3, vt5);
    VROTRI_W(vt5, vt2, 25);
    VXOR_V(vt3, vt3, vt5);               // sigma1(e0)
    VSHUF4I_W(vt5, src, 0x00);           // f0
    VSHUF4I_W(vt1, dst, 0x55);           // g0
    VBITSEL_V(vt5, vt1, vt5, vt2);       // ch(e0,f0,g0)
    VSHUF4I_W(vt1, vt0, 0x00);           // msg0+h0
    VADD_W(vt5, vt5, vt3);
    VADD_W(vt5, vt5, vt1);               // t1_0
    VSHUF4I_W(vt2, dst, 0xaa);           // d0
    VADD_W(vt2, vt2, vt5);               // e1
    VADD_W(vt1, vt4, vt5);               // a1

    // save c0 before dst is reused as a scratch register in round 2
    VSHUF4I_W(vt3, dst, 0xff);           // c0

    // round 2 t1 = sigma1(e1) + ch(e1,e0,f0) + msg1+h1
    VSHUF4I_W(vt5, src, 0x55);           // e0
    VROTRI_W(vt4, vt2, 6);
    VROTRI_W(dst, vt2, 11);
    VXOR_V(vt4, vt4, dst);
    VROTRI_W(dst, vt2, 25);
    VXOR_V(vt4, vt4, dst);               // sigma1(e1)
    VSHUF4I_W(dst, src, 0x00);           // f0
    VBITSEL_V(dst, dst, vt5, vt2);       // ch(e1,e0,f0)
    VSHUF4I_W(vt5, vt0, 0x55);           // msg1+h1
    VADD_W(vt5, vt5, dst);
    VADD_W(vt5, vt5, vt4);               // t1_1
    VADD_W(vt3, vt3, vt5);               // e2

    // round 2 t2 = sigma0(a1) + maj(a1,a0,b0)
    VROTRI_W(vt4, vt1, 2);
    VROTRI_W(dst, vt1, 13);
    VXOR_V(vt4, vt4, dst);
    VROTRI_W(dst, vt1, 22);
    VXOR_V(vt4, vt4, dst);               // sigma0(a1)
    VSHUF4I_W(dst, src, 0xff);           // a0
    VAND_V(dst, dst, vt1);               // a0 & a1
    VSHUF4I_W(xmm0, src, 0xaa);          // b0
    VAND_V(xmm0, xmm0, vt1);             // b0 & a1
    VXOR_V(dst, dst, xmm0);
    VSHUF4I_W(xmm0, src, 0xaa);          // b0
    VSHUF4I_W(vt0, src, 0xff);           // a0
    VAND_V(xmm0, xmm0, vt0);             // b0 & a0
    VXOR_V(dst, dst, xmm0);              // maj(a1,a0,b0)
    VADD_W(vt4, vt4, dst);               // t2_1
    VADD_W(vt4, vt4, vt5);               // a2

    // dst = [f2,e2,b2,a2] = [e1,e2,a1,a2]
    VILVL_W(dst, vt3, vt2);
    VILVL_W(vt5, vt4, vt1);
    VPICKEV_D(dst, vt5, dst);
}

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
