#include "ethjet.h"

#include <gmp.h>
#include <stdio.h>

#include <mutex>

#include <libff/algebra/fields/bigint.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_init.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_g1.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_g2.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_pairing.hpp>
#include <libff/common/profiling.hpp>

using namespace libff;

// Invalid input is reported by returning false, not by an exception: the wasm build has
// no C++ exceptions.
namespace ethjet_ff {
  // libff's parameters are globals, meant to be set up once: setting them up again on
  // every call, as this did, corrupted the heap now and then
  void init() {
    static std::once_flag once;
    std::call_once(once, [] {
      libff::inhibit_profiling_info     = true;
      libff::inhibit_profiling_counters = true;
      init_alt_bn128_params();
    });
  }

  // for loading an element of F_q (a coordinate of G_1)
  // consumes 32 bytes
  bool read_Fq_element (uint8_t *in, alt_bn128_Fq &out) {
    mpz_t x_data, q;
    mpz_init(x_data);
    mpz_init(q);
    mpz_import(x_data, 32, 1, sizeof(in[0]), 1, 0, in);
    alt_bn128_modulus_q.to_mpz(q);
    const mp_size_t limbs = alt_bn128_q_limbs;

    bool ok = mpz_cmp(x_data, q) < 0;
    if (ok)
      out = Fp_model<limbs, alt_bn128_modulus_q>(bigint<limbs>(x_data));
    mpz_clear(x_data);
    mpz_clear(q);
    return ok;
  }

  // for loading an element of F_{q^2} (a coordinate of G_2)
  // consumes 64 bytes
  bool read_Fq2_element (uint8_t *in, alt_bn128_Fq2 &out) {
    // suprising "big-endian" encoding
    alt_bn128_Fq x0, x1;
    if (!read_Fq_element(in+32, x0) || !read_Fq_element(in, x1))
      return false;
    out = Fp2_model<alt_bn128_q_limbs, alt_bn128_modulus_q>(x0, x1);
    return true;
  }

  // for loading an element of F_r (a scalar for G_1)
  // consumes 32 bytes
  alt_bn128_Fr read_Fr_element (uint8_t *in) {
    mpz_t x_data;
    mpz_init(x_data);
    mpz_import(x_data, 32, 1, sizeof(in[0]), 1, 0, in);

    const mp_size_t limbs = alt_bn128_r_limbs;

    alt_bn128_Fr r = Fp_model<limbs, alt_bn128_modulus_r>(bigint<limbs>(x_data));
    mpz_clear(x_data);
    return r;
  }

  // for loading a point in G_1
  // consumes 64 bytes
  bool read_G1_point (uint8_t *in, alt_bn128_G1 &out) {
    alt_bn128_Fq ax, ay;
    if (!read_Fq_element(in, ax) || !read_Fq_element(in+32, ay))
      return false;
    // create curve point from affine coordinates
    // the point at infinity (0,0) is a special case
    if (ax.is_zero() && ay.is_zero()) {
      out = alt_bn128_G1::G1_zero;
    }
    else {
      out = alt_bn128_G1(ax, ay, alt_bn128_Fq::one());
    }
    return out.is_well_formed();
  }

  // for loading a point in G_2
  // consumes 128 bytes
  bool read_G2_point (uint8_t *in, alt_bn128_G2 &out) {
    alt_bn128_Fq2 ax, ay;
    if (!read_Fq2_element(in, ax) || !read_Fq2_element(in+64, ay))
      return false;
    // create curve point from affine coordinates
    // the point at infinity (0,0) is a special case
    if (ax.is_zero() && ay.is_zero()) {
      out = alt_bn128_G2::G2_zero;
      return true;
    }
    out = alt_bn128_G2(ax, ay, alt_bn128_Fq2::one());
    if (! out.is_well_formed())
      return false;
    // additionally check that the element has the right order
    return -alt_bn128_Fr::one() * out + out == alt_bn128_G2::G2_zero;
  }

  // writes an element of Fq, which is less than q and so fits
  // produces 32 bytes
  void write_Fq_element(uint8_t *out, alt_bn128_Fq x) {
    mpz_t x_data;
    mpz_init(x_data);
    x.as_bigint().to_mpz(x_data);

    uint8_t x_arr[32];
    size_t x_size = 0;
    mpz_export(x_arr, &x_size, 1, 1, 1, 0, x_data);
    mpz_clear(x_data);
    // copy the result to the output buffer
    // with padding
    for (size_t i = 1; i <= 32; i++) {
      if (i <= x_size)
        out[32-i] = x_arr[x_size-i];
      else
        out[32-i] = 0;
    }
  }

  // writes a point of G1
  // produces 64 bytes
  void write_G1_point(uint8_t *out, alt_bn128_G1 a) {
    // point at infinity is represented as (0,0)
    // so treat it as a special case
    if (a.is_zero()) {
      write_Fq_element(out,    alt_bn128_Fq::zero());
      write_Fq_element(out+32, alt_bn128_Fq::zero());
      return;
    }
    a.to_affine_coordinates();
    write_Fq_element(out,    a.X);
    write_Fq_element(out+32, a.Y);
  }

  // writes a bool
  // produces 32 bytes
  void write_bool(uint8_t *out, bool p) {
    out[31] = (int)(p);
    for (int i = 2; i <= 32; i++) {
      out[32-i] = 0;
    }
  }
}

extern "C" {
  using namespace ethjet_ff;

  int
  ethjet_ecadd (uint8_t *in, size_t in_size,
                uint8_t *out, size_t out_size) {

    if (in_size != 128) {
      return 0;
    }
    if (out_size != 64) {
      return 0;
    }

    init();

    alt_bn128_G1 a, b;
    if (!read_G1_point(in, a) || !read_G1_point(in+64, b))
      return 0;
    write_G1_point(out, a + b);
    return 1;
  }

  int
  ethjet_ecmul (uint8_t *in, size_t in_size,
                uint8_t *out, size_t out_size) {

    if (in_size != 96) {
      return 0;
    }
    if (out_size != 64) {
      return 0;
    }

    init();

    alt_bn128_G1 a;
    if (!read_G1_point(in, a))
      return 0;
    alt_bn128_Fr n = read_Fr_element(in+64);
    write_G1_point(out, n * a);
    return 1;
  }

  int
  ethjet_ecpairing (uint8_t *in, size_t in_size,
                    uint8_t *out, size_t out_size) {

    if (in_size % 192 != 0)
      return 0;

    if (out_size != 32)
      return 0;

    init();
    int pairs = in_size / 192;

    alt_bn128_Fq12 x = libff::alt_bn128_Fq12::one();
    for (int i = 0; i < pairs; i++) {
      alt_bn128_G1 a;
      alt_bn128_G2 b;
      if (!read_G1_point(in + i*192, a) || !read_G2_point(in + i*192 + 64, b))
        return 0;
      if (a.is_zero() || b.is_zero())
        continue;
      x = x * alt_bn128_miller_loop(alt_bn128_precompute_G1(a), alt_bn128_precompute_G2(b));
    }
    bool result;
    if (pairs == 0)
      result = true;
    else
      result = (alt_bn128_final_exponentiation(x) == alt_bn128_GT::one());
    write_bool(out, result);
    return 1;
  }
}
