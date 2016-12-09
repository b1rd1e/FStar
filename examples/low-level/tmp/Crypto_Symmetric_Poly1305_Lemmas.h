/* This file auto-generated by KreMLin! */
#ifndef __Crypto_Symmetric_Poly1305_Lemmas_H
#define __Crypto_Symmetric_Poly1305_Lemmas_H


#include "Prims.h"
#include "FStar_Mul.h"
#include "FStar_Squash.h"
#include "FStar_StrongExcludedMiddle.h"
#include "FStar_List_Tot.h"
#include "FStar_Classical.h"
#include "FStar_ListProperties.h"
#include "FStar_SeqProperties.h"
#include "FStar_Math_Lemmas.h"
#include "FStar_BitVector.h"
#include "FStar_UInt.h"
#include "FStar_Int.h"
#include "FStar_FunctionalExtensionality.h"
#include "FStar_PropositionalExtensionality.h"
#include "FStar_PredicateExtensionality.h"
#include "FStar_TSet.h"
#include "FStar_Set.h"
#include "FStar_Map.h"
#include "FStar_Ghost.h"
#include "FStar_All.h"
#include "FStar_Bytes.h"
#include "FStar_Buffer.h"
#include "Buffer_Utils.h"
#include "Crypto_Symmetric_Bytes.h"
#include "Crypto_Symmetric_Poly1305_Spec.h"
#include "Crypto_Symmetric_Poly1305_Parameters.h"
#include "Crypto_Symmetric_Poly1305_Bigint.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.h"
#include "FStar_Buffer_Quantifiers.h"
#include "Crypto_Indexing.h"
#include "Flag.h"
#include "Crypto_Symmetric_AES.h"
#include "Intrinsics.h"
#include "Crypto_Symmetric_AES128.h"
#include "Crypto_Symmetric_Chacha20.h"
#include "Crypto_Symmetric_Cipher.h"
#include "kremlib.h"
#include "testlib.h"

void Crypto_Symmetric_Poly1305_Lemmas_pow2_8_lemma(Prims_nat n);

void Crypto_Symmetric_Poly1305_Lemmas_pow2_32_lemma(Prims_nat n);

void Crypto_Symmetric_Poly1305_Lemmas_pow2_64_lemma(Prims_nat n);

typedef uint64_t Crypto_Symmetric_Poly1305_Lemmas_u64_32;

void Crypto_Symmetric_Poly1305_Lemmas_lemma_div_pow2_lt(Prims_nat x, Prims_nat n, Prims_nat m);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_0_0(Prims_nat n, Prims_nat m);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_0(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_div_pow2_mod(Prims_nat a, Prims_nat m, Prims_nat n);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_1_0(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_1(Prims_nat x);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_2(Prims_nat x);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_3(Prims_nat x);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2_4(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_2(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_mod_pow2(Prims_nat a, Prims_nat b, Prims_nat c);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_disjoint_bounded(
  uint64_t b0,
  uint64_t b1,
  Prims_nat l,
  Prims_pos m,
  Prims_nat n
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_3(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
);

Prims_nat Crypto_Symmetric_Poly1305_Lemmas_little_endian_from_top(void *s, Prims_nat len);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_from_top_(void *s, Prims_nat len);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_from_top(void *s);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_from_top_def(void *s, Prims_nat len);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_of_u64(uint64_t u, void *w);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_toField_1(
  uint8_t *s,
  FStar_HyperStack_mem h,
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_eval_5(FStar_HyperStack_mem h, uint64_t *a);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_16(FStar_HyperStack_mem h, uint8_t *a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_mul_mod(Prims_nat a, Prims_pos b);

void
Crypto_Symmetric_Poly1305_Lemmas_add_disjoint_bounded(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat m,
  Prims_nat n
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_0(uint64_t a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_1(uint64_t a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_2(uint64_t a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_3(uint64_t a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_4(uint64_t a);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_norm_5(FStar_HyperStack_mem h, uint64_t *b);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_mod_sum_mul(
  Prims_nat x,
  Prims_nat y,
  Prims_nat l,
  Prims_nat m
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_b3(uint64_t a0, uint64_t a1);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_b6(uint64_t a1, uint64_t a2);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_b9(uint64_t a2, uint64_t a3);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_4(
  Prims_int a,
  Prims_int b,
  Prims_int c,
  Prims_int d,
  Prims_int e
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_3(
  Prims_int a,
  Prims_int b,
  Prims_int c,
  Prims_int d
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_4_1(
  Prims_int b,
  Prims_int c,
  Prims_int d,
  Prims_int e
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_4_2(
  Prims_int b,
  Prims_int c,
  Prims_int d,
  Prims_int e
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_4_3(
  Prims_int b,
  Prims_int c,
  Prims_int d,
  Prims_int e
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_distr_4_4(Prims_int b, Prims_int c, Prims_int d);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_b03a0(
  uint64_t a0,
  uint64_t a1,
  uint8_t b0,
  uint8_t b1,
  uint8_t b2,
  uint8_t b3
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_b46a1(
  uint64_t a1,
  uint64_t a2,
  Prims_int v3,
  uint8_t b4,
  uint8_t b5,
  uint8_t b6
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_b79a2(
  uint64_t a2,
  uint64_t a3,
  Prims_int v6,
  uint8_t b7,
  uint8_t b8,
  uint8_t b9
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_b1012a3(
  uint64_t a3,
  Prims_int v9,
  uint8_t b10,
  uint8_t b11,
  uint8_t b12
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_b1315a4(
  uint64_t a4,
  uint8_t b13,
  uint8_t b14,
  uint8_t b15
);

typedef uint64_t Crypto_Symmetric_Poly1305_Lemmas_u26;

void Crypto_Symmetric_Poly1305_Lemmas_lemma_sub(Prims_int a, Prims_int b, Prims_int c);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_paren(
  Prims_int a,
  Prims_int b,
  Prims_int c,
  Prims_int d
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_sum_(
  Prims_int a,
  Prims_int b,
  Prims_int c,
  Prims_int d,
  Prims_int e,
  Prims_int f,
  Prims_int g,
  Prims_int h
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_sum_0(
  Prims_int b0,
  Prims_int b1,
  Prims_int b2,
  Prims_int b3,
  Prims_int b4,
  Prims_int b5,
  Prims_int b6,
  Prims_int b7,
  Prims_int b8,
  Prims_int b9,
  Prims_int b10,
  Prims_int b11,
  Prims_int b12,
  Prims_int b13,
  Prims_int b14,
  Prims_int b15
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305_(
  uint64_t a0,
  uint64_t a1,
  uint64_t a2,
  uint64_t a3,
  uint64_t a4,
  uint8_t b0,
  uint8_t b1,
  uint8_t b2,
  uint8_t b3,
  uint8_t b4,
  uint8_t b5,
  uint8_t b6,
  uint8_t b7,
  uint8_t b8,
  uint8_t b9,
  uint8_t b10,
  uint8_t b11,
  uint8_t b12,
  uint8_t b13,
  uint8_t b14,
  uint8_t b15
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_mult_le_left(Prims_nat a, Prims_nat b, Prims_nat c);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_eval_mod(
  uint64_t a0,
  uint64_t a1,
  uint64_t a2,
  uint64_t a3,
  uint64_t a4
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_trunc1305(
  FStar_HyperStack_mem hb,
  uint8_t *b,
  FStar_HyperStack_mem ha,
  uint64_t *a
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_little_endian_4(FStar_HyperStack_mem h, uint8_t *b);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_as_seq_sub(
  FStar_HyperStack_mem h,
  uint8_t *b,
  uint32_t i,
  uint32_t len
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word_1(
  FStar_HyperStack_mem ha,
  uint8_t *a,
  uint64_t a0,
  uint64_t a4,
  uint64_t a8,
  uint64_t a12
);

Prims_nat
Crypto_Symmetric_Poly1305_Lemmas_eval_4(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word_2_2(
  uint64_t a0,
  uint64_t a1,
  uint64_t a2,
  uint64_t a3,
  uint64_t b0,
  uint64_t b1,
  uint64_t b2,
  uint64_t b3
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word_2_1(
  uint64_t a0,
  uint64_t a4,
  uint64_t a8,
  uint64_t a12,
  uint64_t b0,
  uint64_t b4,
  uint64_t b8,
  uint64_t b12
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word_2(
  uint64_t a0,
  uint64_t a4,
  uint64_t a8,
  uint64_t a12,
  uint64_t b0,
  uint64_t b4,
  uint64_t b8,
  uint64_t b12
);

bool
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word_post(
  uint64_t a0,
  uint64_t a4,
  uint64_t a8,
  uint64_t a12,
  uint64_t b0,
  uint64_t b4,
  uint64_t b8,
  uint64_t b12,
  FStar_HyperStack_mem ha,
  uint8_t *a,
  FStar_HyperStack_mem hb,
  uint8_t *b
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word(
  FStar_HyperStack_mem ha,
  uint8_t *a,
  FStar_HyperStack_mem hb,
  uint8_t *b,
  uint64_t a0,
  uint64_t a4,
  uint64_t a8,
  uint64_t a12,
  uint64_t b0,
  uint64_t b4,
  uint64_t b8,
  uint64_t b12
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word2_1(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4,
  uint8_t *b,
  uint32_t z0,
  uint32_t z1,
  uint32_t z2,
  uint32_t z3
);

void Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word2_2_1(uint32_t z);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word2_2(
  FStar_HyperStack_mem ha,
  uint8_t *a,
  uint32_t z0,
  uint32_t z1,
  uint32_t z2,
  uint32_t z3
);

void
Crypto_Symmetric_Poly1305_Lemmas_lemma_add_word2(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4,
  uint8_t *b,
  uint32_t z0,
  uint32_t z1,
  uint32_t z2,
  uint32_t z3
);
#endif
