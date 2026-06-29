#include "ethjet-bls.h"
#include <blst.h>
#include <string.h>
#include <stdlib.h>

/* EIP-2537 encoding sizes */
#define FP_SIZE           48
#define FP_PADDING        16
#define FP_PADDED_SIZE    (FP_PADDING + FP_SIZE)   /* 64 */
#define SCALAR_SIZE       32
#define G1_POINT_SIZE     (2 * FP_PADDED_SIZE)     /* 128 */
#define G2_POINT_SIZE     (4 * FP_PADDED_SIZE)     /* 256 */
#define G1_SCALAR_PAIR    (G1_POINT_SIZE + SCALAR_SIZE)  /* 160 */
#define G2_SCALAR_PAIR    (G2_POINT_SIZE + SCALAR_SIZE)  /* 288 */
#define PAIRING_PAIR      (G1_POINT_SIZE + G2_POINT_SIZE) /* 384 */

/* BLS12-381 field modulus p (big-endian)
 * p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
 */
static const uint8_t BLS_MODULUS[48] = {
    0x1a, 0x01, 0x11, 0xea, 0x39, 0x7f, 0xe6, 0x9a,
    0x4b, 0x1b, 0xa7, 0xb6, 0x43, 0x4b, 0xac, 0xd7,
    0x64, 0x77, 0x4b, 0x84, 0xf3, 0x85, 0x12, 0xbf,
    0x67, 0x30, 0xd2, 0xa0, 0xf6, 0xb0, 0xf6, 0x24,
    0x1e, 0xab, 0xff, 0xfe, 0xb1, 0x53, 0xff, 0xff,
    0xb9, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xaa, 0xab
};

/* Compare two big-endian byte arrays, returns:
 * -1 if a < b, 0 if a == b, 1 if a > b */
static int compare_be(const uint8_t *a, const uint8_t *b, size_t len) {
    for (size_t i = 0; i < len; i++) {
        if (a[i] < b[i]) return -1;
        if (a[i] > b[i]) return 1;
    }
    return 0;
}

/* Check if all bytes are zero */
static int is_zero(const uint8_t *data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        if (data[i] != 0) return 0;
    }
    return 1;
}

/* Reverse byte order of a 32-byte scalar (big-endian to little-endian)
 * blst expects little-endian scalars but EIP-2537 specifies big-endian */
static void reverse_scalar_32(uint8_t *out, const uint8_t *in) {
    for (int i = 0; i < SCALAR_SIZE; i++) {
        out[i] = in[SCALAR_SIZE - 1 - i];
    }
}

/* Validate a 64-byte Fp element (16 byte padding + 48 byte value)
 * Returns 1 if valid (padding is zero and value < modulus), 0 otherwise */
static int is_valid_fp(const uint8_t *fp64) {
    /* First 16 bytes must be zero padding */
    if (!is_zero(fp64, FP_PADDING)) return 0;

    /* Remaining 48 bytes must be < modulus */
    if (compare_be(fp64 + FP_PADDING, BLS_MODULUS, FP_SIZE) >= 0) return 0;

    return 1;
}

/* Validate a 128-byte Fp2 element (c0(64) || c1(64))
 * Returns 1 if valid, 0 otherwise */
static int is_valid_fp2(const uint8_t *fp2_128) {
    return is_valid_fp(fp2_128) && is_valid_fp(fp2_128 + FP_PADDED_SIZE);
}

/* Decode a 128-byte G1 point from EIP-2537 format
 * Format: x(64) || y(64), where each Fp is 16 byte padding + 48 byte value
 * Returns 1 on success, 0 on failure
 * If subgroup_check is true, also verifies the point is in G1 subgroup */
static int decode_g1_point(blst_p1_affine *out, const uint8_t *in128, int subgroup_check) {
    /* Validate field elements */
    if (!is_valid_fp(in128)) {
        return 0;
    }
    if (!is_valid_fp(in128 + FP_PADDED_SIZE)) {
        return 0;
    }

    /* Check for point at infinity (all zeros) */
    if (is_zero(in128, G1_POINT_SIZE)) {
        memset(out, 0, sizeof(*out));
        return 1;
    }

    /* Decode x coordinate (skip 16 byte padding) */
    blst_fp_from_bendian(&out->x, in128 + FP_PADDING);

    /* Decode y coordinate (skip 16 byte padding) */
    blst_fp_from_bendian(&out->y, in128 + FP_PADDED_SIZE + FP_PADDING);

    /* Check point is on curve */
    if (!blst_p1_affine_on_curve(out)) {
        return 0;
    }

    /* Check subgroup membership if required */
    if (subgroup_check && !blst_p1_affine_in_g1(out)) {
        return 0;
    }

    return 1;
}

/* Decode a 256-byte G2 point from EIP-2537 format
 * Format: x(128) || y(128), where x and y are Fp2 = c0(64) || c1(64)
 * Returns 1 on success, 0 on failure */
static int decode_g2_point(blst_p2_affine *out, const uint8_t *in256, int subgroup_check) {
    /* Validate field elements */
    if (!is_valid_fp2(in256) || !is_valid_fp2(in256 + 2 * FP_PADDED_SIZE)) {
        return 0;
    }

    /* Check for point at infinity (all zeros) */
    if (is_zero(in256, G2_POINT_SIZE)) {
        memset(out, 0, sizeof(*out));
        return 1;
    }

    /* Decode x coordinate (Fp2 = c0 || c1)
     * EIP-2537: element is c0 + i*c1, encoded as c0 || c1
     * blst: fp[0] is c0 (real), fp[1] is c1 (imaginary) */
    blst_fp_from_bendian(&out->x.fp[0], in256 + FP_PADDING);       /* x.c0 (real) */
    blst_fp_from_bendian(&out->x.fp[1], in256 + FP_PADDED_SIZE + FP_PADDING);  /* x.c1 (imag) */

    /* Decode y coordinate */
    blst_fp_from_bendian(&out->y.fp[0], in256 + 2 * FP_PADDED_SIZE + FP_PADDING);       /* y.c0 (real) */
    blst_fp_from_bendian(&out->y.fp[1], in256 + 3 * FP_PADDED_SIZE + FP_PADDING);  /* y.c1 (imag) */

    /* Check point is on curve */
    if (!blst_p2_affine_on_curve(out)) {
        return 0;
    }

    /* Check subgroup membership if required */
    if (subgroup_check && !blst_p2_affine_in_g2(out)) {
        return 0;
    }

    return 1;
}

/* Encode a G1 point to 128-byte EIP-2537 format */
static void encode_g1_point(uint8_t *out128, const blst_p1 *p) {
    blst_p1_affine affine;
    blst_p1_to_affine(&affine, p);

    /* Check for point at infinity */
    if (blst_p1_affine_is_inf(&affine)) {
        memset(out128, 0, G1_POINT_SIZE);
        return;
    }

    /* Encode x with 16 byte zero padding */
    memset(out128, 0, FP_PADDING);
    blst_bendian_from_fp(out128 + FP_PADDING, &affine.x);

    /* Encode y with 16 byte zero padding */
    memset(out128 + FP_PADDED_SIZE, 0, FP_PADDING);
    blst_bendian_from_fp(out128 + FP_PADDED_SIZE + FP_PADDING, &affine.y);
}

/* Encode a G2 affine point directly to 256-byte EIP-2537 format */
static void encode_g2_point_affine(uint8_t *out256, const blst_p2_affine *affine) {
    /* Check for point at infinity */
    if (blst_p2_affine_is_inf(affine)) {
        memset(out256, 0, G2_POINT_SIZE);
        return;
    }

    /* Encode x.c0 with padding */
    memset(out256, 0, FP_PADDING);
    blst_bendian_from_fp(out256 + FP_PADDING, &affine->x.fp[0]);

    /* Encode x.c1 with padding */
    memset(out256 + FP_PADDED_SIZE, 0, FP_PADDING);
    blst_bendian_from_fp(out256 + FP_PADDED_SIZE + FP_PADDING, &affine->x.fp[1]);

    /* Encode y.c0 with padding */
    memset(out256 + 2 * FP_PADDED_SIZE, 0, FP_PADDING);
    blst_bendian_from_fp(out256 + 2 * FP_PADDED_SIZE + FP_PADDING, &affine->y.fp[0]);

    /* Encode y.c1 with padding */
    memset(out256 + 3 * FP_PADDED_SIZE, 0, FP_PADDING);
    blst_bendian_from_fp(out256 + 3 * FP_PADDED_SIZE + FP_PADDING, &affine->y.fp[1]);
}

/* Encode a G2 point to 256-byte EIP-2537 format */
static void encode_g2_point(uint8_t *out256, const blst_p2 *p) {
    blst_p2_affine affine;
    blst_p2_to_affine(&affine, p);
    encode_g2_point_affine(out256, &affine);
}

/* G1ADD: Add two G1 points */
int ethjet_bls_g1add(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != 2 * G1_POINT_SIZE || out_size < G1_POINT_SIZE) {
        return 0;
    }

    blst_p1_affine a_affine, b_affine;

    /* Decode input points (no subgroup check for ADD) */
    if (!decode_g1_point(&a_affine, in, 0)) return 0;
    if (!decode_g1_point(&b_affine, in + G1_POINT_SIZE, 0)) return 0;

    /* Convert to projective and add */
    blst_p1 a, result;
    blst_p1_from_affine(&a, &a_affine);
    blst_p1_add_or_double_affine(&result, &a, &b_affine);

    /* Encode result */
    encode_g1_point(out, &result);

    return 1;
}

/* G1MUL: Multiply G1 point by scalar */
int ethjet_bls_g1mul(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != G1_SCALAR_PAIR || out_size < G1_POINT_SIZE) {
        return 0;
    }

    blst_p1_affine p_affine;

    /* Decode point (no subgroup check for MUL) */
    if (!decode_g1_point(&p_affine, in, 0)) return 0;

    /* Convert scalar from big-endian to little-endian */
    uint8_t scalar_le[32];
    reverse_scalar_32(scalar_le, in + G1_POINT_SIZE);

    /* Convert to projective and multiply */
    blst_p1 p, result;
    blst_p1_from_affine(&p, &p_affine);
    blst_p1_mult(&result, &p, scalar_le, 256);

    /* Encode result */
    encode_g1_point(out, &result);

    return 1;
}

/* G1MSM: Multi-scalar multiplication on G1
 * Points at infinity are filtered out (they contribute 0 to the sum) */
int ethjet_bls_g1msm(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (out_size < G1_POINT_SIZE) {
        return 0;
    }
    if (in_size == 0 || in_size % G1_SCALAR_PAIR != 0) {
        return 0;
    }

    size_t k = in_size / G1_SCALAR_PAIR;

    /* Empty input: EIP-2537 requires error for empty input */
    if (k == 0) {
        return 0;
    }

    /* Allocate arrays for points and scalars */
    blst_p1_affine *points = malloc(k * sizeof(blst_p1_affine));
    const blst_p1_affine **point_ptrs = malloc(k * sizeof(blst_p1_affine*));
    uint8_t *scalars_le = malloc(k * SCALAR_SIZE);  /* Converted little-endian scalars */
    const uint8_t **scalar_ptrs = malloc(k * sizeof(uint8_t*));

    if (!points || !point_ptrs || !scalars_le || !scalar_ptrs) {
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 0;
    }

    /* Decode all points (with subgroup check for MSM) and convert scalars
     * Filter out infinity points - they contribute 0 to the sum */
    size_t valid_pairs = 0;
    for (size_t i = 0; i < k; i++) {
        if (!decode_g1_point(&points[valid_pairs], in + i * G1_SCALAR_PAIR, 1)) {
            free(points);
            free(point_ptrs);
            free(scalars_le);
            free(scalar_ptrs);
            return 0;
        }

        /* Skip infinity points - they contribute 0 to the MSM sum */
        if (blst_p1_affine_is_inf(&points[valid_pairs])) {
            continue;
        }

        point_ptrs[valid_pairs] = &points[valid_pairs];
        /* Convert scalar from big-endian to little-endian */
        reverse_scalar_32(scalars_le + valid_pairs * SCALAR_SIZE, in + i * G1_SCALAR_PAIR + G1_POINT_SIZE);
        scalar_ptrs[valid_pairs] = scalars_le + valid_pairs * SCALAR_SIZE;
        valid_pairs++;
    }

    /* If all points are infinity, return infinity */
    if (valid_pairs == 0) {
        memset(out, 0, G1_POINT_SIZE);
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 1;
    }

    /* Perform MSM using Pippenger algorithm */
    blst_p1 result;
    size_t scratch_size = blst_p1s_mult_pippenger_scratch_sizeof(valid_pairs);
    limb_t *scratch = malloc(scratch_size);

    if (!scratch) {
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 0;
    }

    blst_p1s_mult_pippenger(&result, point_ptrs, valid_pairs, scalar_ptrs, 256, scratch);

    /* Encode result */
    encode_g1_point(out, &result);

    free(scratch);
    free(points);
    free(point_ptrs);
    free(scalars_le);
    free(scalar_ptrs);

    return 1;
}

/* G2ADD: Add two G2 points */
int ethjet_bls_g2add(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != 2 * G2_POINT_SIZE || out_size < G2_POINT_SIZE) {
        return 0;
    }

    blst_p2_affine a_affine, b_affine;

    /* Decode input points (no subgroup check for ADD) */
    if (!decode_g2_point(&a_affine, in, 0)) return 0;
    if (!decode_g2_point(&b_affine, in + G2_POINT_SIZE, 0)) return 0;

    /* Handle infinity cases explicitly */
    int a_is_inf = blst_p2_affine_is_inf(&a_affine);
    int b_is_inf = blst_p2_affine_is_inf(&b_affine);

    if (a_is_inf && b_is_inf) {
        /* inf + inf = inf */
        memset(out, 0, G2_POINT_SIZE);
        return 1;
    } else if (a_is_inf) {
        /* inf + B = B */
        encode_g2_point_affine(out, &b_affine);
        return 1;
    } else if (b_is_inf) {
        /* A + inf = A */
        encode_g2_point_affine(out, &a_affine);
        return 1;
    }

    /* Convert to projective and add */
    blst_p2 a, result;
    blst_p2_from_affine(&a, &a_affine);
    blst_p2_add_or_double_affine(&result, &a, &b_affine);

    /* Encode result */
    encode_g2_point(out, &result);

    return 1;
}

/* G2MUL: Multiply G2 point by scalar */
int ethjet_bls_g2mul(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != G2_SCALAR_PAIR || out_size < G2_POINT_SIZE) {
        return 0;
    }

    blst_p2_affine p_affine;

    /* Decode point (no subgroup check for MUL) */
    if (!decode_g2_point(&p_affine, in, 0)) return 0;

    /* Convert scalar from big-endian to little-endian */
    uint8_t scalar_le[32];
    reverse_scalar_32(scalar_le, in + G2_POINT_SIZE);

    /* Convert to projective and multiply */
    blst_p2 p, result;
    blst_p2_from_affine(&p, &p_affine);
    blst_p2_mult(&result, &p, scalar_le, 256);

    /* Encode result */
    encode_g2_point(out, &result);

    return 1;
}

/* G2MSM: Multi-scalar multiplication on G2
 * Points at infinity are filtered out (they contribute 0 to the sum) */
int ethjet_bls_g2msm(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (out_size < G2_POINT_SIZE) return 0;
    if (in_size == 0 || in_size % G2_SCALAR_PAIR != 0) return 0;

    size_t k = in_size / G2_SCALAR_PAIR;

    /* Empty input: EIP-2537 requires error for empty input */
    if (k == 0) {
        return 0;
    }

    /* Allocate arrays for points and scalars */
    blst_p2_affine *points = malloc(k * sizeof(blst_p2_affine));
    const blst_p2_affine **point_ptrs = malloc(k * sizeof(blst_p2_affine*));
    uint8_t *scalars_le = malloc(k * SCALAR_SIZE);  /* Converted little-endian scalars */
    const uint8_t **scalar_ptrs = malloc(k * sizeof(uint8_t*));

    if (!points || !point_ptrs || !scalars_le || !scalar_ptrs) {
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 0;
    }

    /* Decode all points (with subgroup check for MSM) and convert scalars
     * Filter out infinity points - they contribute 0 to the sum */
    size_t valid_pairs = 0;
    for (size_t i = 0; i < k; i++) {
        if (!decode_g2_point(&points[valid_pairs], in + i * G2_SCALAR_PAIR, 1)) {
            free(points);
            free(point_ptrs);
            free(scalars_le);
            free(scalar_ptrs);
            return 0;
        }

        /* Skip infinity points - they contribute 0 to the MSM sum */
        if (blst_p2_affine_is_inf(&points[valid_pairs])) {
            continue;
        }

        point_ptrs[valid_pairs] = &points[valid_pairs];
        /* Convert scalar from big-endian to little-endian */
        reverse_scalar_32(scalars_le + valid_pairs * SCALAR_SIZE, in + i * G2_SCALAR_PAIR + G2_POINT_SIZE);
        scalar_ptrs[valid_pairs] = scalars_le + valid_pairs * SCALAR_SIZE;
        valid_pairs++;
    }

    /* If all points are infinity, return infinity */
    if (valid_pairs == 0) {
        memset(out, 0, G2_POINT_SIZE);
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 1;
    }

    /* Perform MSM using Pippenger algorithm */
    blst_p2 result;
    size_t scratch_size = blst_p2s_mult_pippenger_scratch_sizeof(valid_pairs);
    limb_t *scratch = malloc(scratch_size);

    if (!scratch) {
        free(points);
        free(point_ptrs);
        free(scalars_le);
        free(scalar_ptrs);
        return 0;
    }

    blst_p2s_mult_pippenger(&result, point_ptrs, valid_pairs, scalar_ptrs, 256, scratch);

    /* Encode result */
    encode_g2_point(out, &result);

    free(scratch);
    free(points);
    free(point_ptrs);
    free(scalars_le);
    free(scalar_ptrs);

    return 1;
}

/* PAIRING: BLS12-381 pairing check
 * Computes e(P1, Q1) * e(P2, Q2) * ... * e(Pk, Qk) and checks if result equals 1
 * Pairs where either point is infinity are skipped (e(P,0) = e(0,Q) = 1) */
int ethjet_bls_pairing(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (out_size < 32) return 0;
    if (in_size % PAIRING_PAIR != 0) return 0;

    size_t k = in_size / PAIRING_PAIR;

    /* Empty input: EIP-2537 requires error for empty input */
    if (k == 0) {
        return 0;
    }

    /* Allocate arrays for points */
    blst_p1_affine *g1_points = malloc(k * sizeof(blst_p1_affine));
    blst_p2_affine *g2_points = malloc(k * sizeof(blst_p2_affine));
    const blst_p1_affine **g1_ptrs = malloc(k * sizeof(blst_p1_affine*));
    const blst_p2_affine **g2_ptrs = malloc(k * sizeof(blst_p2_affine*));

    if (!g1_points || !g2_points || !g1_ptrs || !g2_ptrs) {
        free(g1_points);
        free(g2_points);
        free(g1_ptrs);
        free(g2_ptrs);
        return 0;
    }

    /* Decode all pairs (with subgroup check for PAIRING) */
    size_t valid_pairs = 0;
    for (size_t i = 0; i < k; i++) {
        /* G1 point: 128 bytes */
        if (!decode_g1_point(&g1_points[valid_pairs], in + i * PAIRING_PAIR, 1)) {
            free(g1_points);
            free(g2_points);
            free(g1_ptrs);
            free(g2_ptrs);
            return 0;
        }
        /* G2 point: 256 bytes */
        if (!decode_g2_point(&g2_points[valid_pairs], in + i * PAIRING_PAIR + G1_POINT_SIZE, 1)) {
            free(g1_points);
            free(g2_points);
            free(g1_ptrs);
            free(g2_ptrs);
            return 0;
        }

        /* Skip pairs where either point is infinity - e(P,0) = e(0,Q) = 1 */
        if (blst_p1_affine_is_inf(&g1_points[valid_pairs]) ||
            blst_p2_affine_is_inf(&g2_points[valid_pairs])) {
            continue;
        }

        g1_ptrs[valid_pairs] = &g1_points[valid_pairs];
        g2_ptrs[valid_pairs] = &g2_points[valid_pairs];
        valid_pairs++;
    }

    /* If all pairs had infinity points, result is 1 */
    if (valid_pairs == 0) {
        memset(out, 0, 31);
        out[31] = 1;
        free(g1_points);
        free(g2_points);
        free(g1_ptrs);
        free(g2_ptrs);
        return 1;
    }

    /* Compute multi-pairing using Miller loop */
    blst_fp12 result;
    blst_miller_loop_n(&result, g2_ptrs, g1_ptrs, valid_pairs);
    blst_final_exp(&result, &result);

    /* Check if result is one */
    int is_one = blst_fp12_is_one(&result);

    /* Output: 32 bytes, value is 1 if pairing check passed, 0 otherwise */
    memset(out, 0, 32);
    if (is_one) {
        out[31] = 1;
    }

    free(g1_points);
    free(g2_points);
    free(g1_ptrs);
    free(g2_ptrs);

    return 1;
}

/* MAP_FP_TO_G1: Map field element to G1 point */
int ethjet_bls_map_fp_to_g1(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != FP_PADDED_SIZE || out_size < G1_POINT_SIZE) {
        return 0;
    }

    /* Validate field element */
    if (!is_valid_fp(in)) {
        return 0;
    }

    /* Decode field element (skip 16 byte padding) */
    blst_fp u;
    blst_fp_from_bendian(&u, in + FP_PADDING);

    /* Map to G1 */
    blst_p1 result;
    blst_map_to_g1(&result, &u, NULL);

    /* Encode result */
    encode_g1_point(out, &result);

    return 1;
}

/* MAP_FP2_TO_G2: Map Fp2 element to G2 point */
int ethjet_bls_map_fp2_to_g2(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size) {
    if (in_size != 2 * FP_PADDED_SIZE || out_size < G2_POINT_SIZE) {
        return 0;
    }

    /* Validate Fp2 element */
    if (!is_valid_fp2(in)) {
        return 0;
    }

    /* Decode Fp2 element (c0 || c1) */
    blst_fp2 u;
    blst_fp_from_bendian(&u.fp[0], in + FP_PADDING);       /* c0 */
    blst_fp_from_bendian(&u.fp[1], in + FP_PADDED_SIZE + FP_PADDING);  /* c1 */

    /* Map to G2 */
    blst_p2 result;
    blst_map_to_g2(&result, &u, NULL);

    /* Encode result */
    encode_g2_point(out, &result);

    return 1;
}
