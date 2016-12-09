/* This file auto-generated by KreMLin! */
#ifndef __Crypto_Symmetric_GF128_Spec_H
#define __Crypto_Symmetric_GF128_Spec_H


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
#include "kremlib.h"
#include "testlib.h"

typedef void *Crypto_Symmetric_GF128_Spec_text;

typedef void *Crypto_Symmetric_GF128_Spec_elem;

extern void *Crypto_Symmetric_GF128_Spec_op_Plus_At(void *x0, void *x1);

extern void *Crypto_Symmetric_GF128_Spec_op_Star_At(void *x0, void *x1);

extern void *Crypto_Symmetric_GF128_Spec_zero;

void *Crypto_Symmetric_GF128_Spec_encode(void *x);

void *Crypto_Symmetric_GF128_Spec_poly(void *vs, void *r);

void *Crypto_Symmetric_GF128_Spec_finish(void *a, void *s);

void *Crypto_Symmetric_GF128_Spec_mac(void *vs, void *r, void *s);
#endif
