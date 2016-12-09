/* This file auto-generated by KreMLin! */
#ifndef __Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_H
#define __Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_H


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
#include "kremlib.h"
#include "testlib.h"

typedef uint64_t Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_u633;

void Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_10_0(Prims_int x, Prims_pos y);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_10_1(
  Prims_nat x,
  Prims_nat y,
  Prims_pos z
);

void Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_10_2(Prims_nat x);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_10(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *b
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_110_0(
  Prims_int x,
  Prims_int y,
  Prims_nat z
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_1101(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat b2,
  Prims_nat b3,
  Prims_nat b4,
  Prims_nat c0,
  Prims_nat c1,
  Prims_nat c2,
  Prims_nat c3,
  Prims_nat c4,
  Prims_nat c5
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_1102(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat b2,
  Prims_nat b3,
  Prims_nat b4,
  Prims_nat c0,
  Prims_nat c1,
  Prims_nat c2,
  Prims_nat c3,
  Prims_nat c4,
  Prims_nat c5
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_1103(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat b2,
  Prims_nat b3,
  Prims_nat b4,
  Prims_nat c0,
  Prims_nat c1,
  Prims_nat c2,
  Prims_nat c3,
  Prims_nat c4,
  Prims_nat c5
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_1104(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat b2,
  Prims_nat b3,
  Prims_nat b4,
  Prims_nat c0,
  Prims_nat c1,
  Prims_nat c2,
  Prims_nat c3,
  Prims_nat c4,
  Prims_nat c5
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_110(
  Prims_nat b0,
  Prims_nat b1,
  Prims_nat b2,
  Prims_nat b3,
  Prims_nat b4,
  Prims_nat c0,
  Prims_nat c1,
  Prims_nat c2,
  Prims_nat c3,
  Prims_nat c4,
  Prims_nat c5
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_11(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *b
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_1(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *b
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_div_lt(
  Prims_nat a,
  Prims_nat n,
  Prims_nat m
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_div_rest(
  Prims_nat a,
  Prims_nat m,
  Prims_nat n
);

void Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_mod_0(Prims_nat a, Prims_pos b);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_20(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *b
);

void
Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4_lemma_carry_2(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *b
);
#endif
