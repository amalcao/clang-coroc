// RUN: %clang_cc1 %s -O0 -triple=x86_64-apple-darwin -target-feature +avx512f -emit-llvm -o - -Werror | FileCheck %s

// Don't include mm_malloc.h, it's system specific.
#define __MM_MALLOC_H

#include <immintrin.h>

__m512d test_mm512_sqrt_pd(__m512d a)
{
  // CHECK-LABEL: @test_mm512_sqrt_pd
  // CHECK: @llvm.x86.avx512.sqrt.pd.512
  return _mm512_sqrt_pd(a);
}

__m512 test_mm512_sqrt_ps(__m512 a)
{
  // CHECK-LABEL: @test_mm512_sqrt_ps
  // CHECK: @llvm.x86.avx512.sqrt.ps.512
  return _mm512_sqrt_ps(a);
}

__m512d test_mm512_rsqrt14_pd(__m512d a)
{
  // CHECK-LABEL: @test_mm512_rsqrt14_pd
  // CHECK: @llvm.x86.avx512.rsqrt14.pd.512
  return _mm512_rsqrt14_pd(a);
}

__m512 test_mm512_rsqrt14_ps(__m512 a)
{
  // CHECK-LABEL: @test_mm512_rsqrt14_ps
  // CHECK: @llvm.x86.avx512.rsqrt14.ps.512
  return _mm512_rsqrt14_ps(a);
}

__m512 test_mm512_add_ps(__m512 a, __m512 b)
{
  // CHECK-LABEL: @test_mm512_add_ps
  // CHECK: fadd <16 x float>
  return _mm512_add_ps(a, b);
}

__m512d test_mm512_add_pd(__m512d a, __m512d b)
{
  // CHECK-LABEL: @test_mm512_add_pd
  // CHECK: fadd <8 x double>
  return _mm512_add_pd(a, b);
}

__m512 test_mm512_mul_ps(__m512 a, __m512 b)
{
  // CHECK-LABEL: @test_mm512_mul_ps
  // CHECK: fmul <16 x float>
  return _mm512_mul_ps(a, b);
}

__m512d test_mm512_mul_pd(__m512d a, __m512d b)
{
  // CHECK-LABEL: @test_mm512_mul_pd
  // CHECK: fmul <8 x double>
  return _mm512_mul_pd(a, b);
}

void test_mm512_storeu_ps(void *p, __m512 a)
{
  // CHECK-LABEL: @test_mm512_storeu_ps
  // CHECK: @llvm.x86.avx512.mask.storeu.ps.512
  _mm512_storeu_ps(p, a);
}

void test_mm512_storeu_pd(void *p, __m512d a)
{
  // CHECK-LABEL: @test_mm512_storeu_pd
  // CHECK: @llvm.x86.avx512.mask.storeu.pd.512
  _mm512_storeu_pd(p, a);
}

void test_mm512_store_ps(void *p, __m512 a)
{
  // CHECK-LABEL: @test_mm512_store_ps
  // CHECK: store <16 x float>
  _mm512_store_ps(p, a);
}

void test_mm512_store_pd(void *p, __m512d a)
{
  // CHECK-LABEL: @test_mm512_store_pd
  // CHECK: store <8 x double>
  _mm512_store_pd(p, a);
}
