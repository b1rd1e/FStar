/* This file auto-generated by KreMLin! */
#ifndef __Crypto_AEAD_H
#define __Crypto_AEAD_H


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
#include "Crypto_Symmetric_Poly1305_Lemmas.h"
#include "Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.h"
#include "Crypto_Symmetric_Poly1305_Bignum.h"
#include "Crypto_Symmetric_Poly1305.h"
#include "Crypto_Symmetric_GF128_Spec.h"
#include "Crypto_Symmetric_GF128.h"
#include "Crypto_Symmetric_MAC.h"
#include "Crypto_Symmetric_UF1CMA.h"
#include "Crypto_Plain.h"
#include "Crypto_Symmetric_PRF.h"
#include "Crypto_AEAD_Encoding.h"
#include "Crypto_AEAD_Invariant.h"
#include "Crypto_AEAD_Lemmas.h"
#include "Crypto_AEAD_Lemmas_Part2.h"
#include "kremlib.h"
#include "testlib.h"

typedef FStar_HyperHeap_rid Crypto_AEAD_region;

uint32_t Crypto_AEAD_ctr(Crypto_Indexing_id uu____15, Crypto_Symmetric_PRF_domain____ x);

void
Crypto_AEAD_mac_wrapper(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
);

extern void Crypto_AEAD_lt_pow2_index_to_vec(Prims_nat x0, FStar_UInt128_t x1);

extern void Crypto_AEAD_index_to_vec_lt_pow2(Prims_nat x0, void *x1);

void Crypto_AEAD_lemma_xor_bounded(Prims_nat n, FStar_UInt128_t x, FStar_UInt128_t y);

FStar_UInt128_t
Crypto_AEAD_aeIV(Crypto_Indexing_id i, uint64_t seqn, FStar_UInt128_t staticIV);

extern void
Crypto_AEAD_aeIV_injective(Crypto_Indexing_id x0, uint64_t x1, uint64_t x2, FStar_UInt128_t x3);

Crypto_AEAD_Invariant_state_______
Crypto_AEAD_genReader(Crypto_Indexing_id i, Crypto_AEAD_Invariant_state_______ st);

uint8_t *Crypto_AEAD_leak(Crypto_Indexing_id i, Crypto_AEAD_Invariant_state_______ st);

void
Crypto_AEAD_counter_enxor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint32_t remaining_len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h_init
);

Crypto_Symmetric_PRF_state____
Crypto_AEAD_prf_state(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ e
);

void
Crypto_AEAD_lemma_frame_find_mac(
  Crypto_Indexing_id i,
  Prims_nat l,
  Crypto_Symmetric_PRF_state____ st,
  Crypto_Symmetric_PRF_domain____ x,
  uint8_t *b,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
);

typedef struct { Prims_nat x00; } FStar_Heap_ref__Prims_nat;

void
Crypto_AEAD_heap_modifies_fresh_empty_0(
  FStar_Heap_heap h0,
  FStar_Heap_heap h1,
  FStar_Heap_heap h2,
  FStar_Heap_ref__Prims_nat x
);

void
Crypto_AEAD_modifies_fresh_empty_0(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperHeap_rid r,
  void *x
);

void
Crypto_AEAD_modifies_fresh_empty(
  Crypto_Indexing_id i,
  FStar_UInt128_t n,
  FStar_HyperHeap_rid r,
  Crypto_Symmetric_UF1CMA_state____ m,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
);

void
Crypto_AEAD_extend_refines_aux(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  Prims_nat len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
);

void
Crypto_AEAD_frame_refines(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  void *entries,
  void *blocks,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h_
);

void
Crypto_AEAD_refines_to_inv(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t len,
  uint8_t *plain,
  uint8_t *cipher
);

void
Crypto_AEAD_finish_after_mac(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h3,
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged,
  Crypto_Symmetric_UF1CMA_state____ ak,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
);

void
Crypto_AEAD_modifies_push_pop(
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h5,
  bool (*r)(FStar_HyperHeap_rid x0)
);

void
Crypto_AEAD_frame_refines_(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  void *entries,
  void *blocks,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h_
);

void
Crypto_AEAD_frame_myinv_push(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h1
);

void
Crypto_AEAD_encrypt_ensures_push_pop(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h5
);

void
Crypto_AEAD_encrypt(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged
);

void
Crypto_AEAD_counter_dexor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint8_t *plaintext,
  uint8_t *ciphertext
);

bool
Crypto_AEAD_decrypt(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t iv,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged
);
#endif
