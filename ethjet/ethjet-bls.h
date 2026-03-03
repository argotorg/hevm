#ifndef ETHJET_BLS_H
#define ETHJET_BLS_H

#include <stdint.h>
#include <stddef.h>

/* BLS12-381 precompile implementations (EIP-2537)
 * All functions return 1 on success, 0 on failure (invalid input or verification failed)
 *
 * EIP-2537 precompile addresses (revised spec):
 * 0x0B = G1ADD
 * 0x0C = G1MSM (handles single scalar multiplication when k=1)
 * 0x0D = G2ADD
 * 0x0E = G2MSM (handles single scalar multiplication when k=1)
 * 0x0F = PAIRING
 * 0x10 = MAP_FP_TO_G1
 * 0x11 = MAP_FP2_TO_G2
 */

/* G1ADD (0x0B): Add two G1 points
 * Input: 256 bytes (2 x 128 byte G1 points)
 * Output: 128 bytes (G1 point) */
int ethjet_bls_g1add(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* G1MSM (0x0C): Multi-scalar multiplication on G1
 * Input: 160*k bytes (k pairs of 128 byte G1 point + 32 byte scalar)
 * Output: 128 bytes (G1 point)
 * Note: For k=1, this is equivalent to scalar multiplication */
int ethjet_bls_g1msm(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* G2ADD (0x0D): Add two G2 points
 * Input: 512 bytes (2 x 256 byte G2 points)
 * Output: 256 bytes (G2 point) */
int ethjet_bls_g2add(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* G2MSM (0x0E): Multi-scalar multiplication on G2
 * Input: 288*k bytes (k pairs of 256 byte G2 point + 32 byte scalar)
 * Output: 256 bytes (G2 point)
 * Note: For k=1, this is equivalent to scalar multiplication */
int ethjet_bls_g2msm(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* PAIRING (0x0F): BLS12-381 pairing check
 * Input: 384*k bytes (k pairs of 128 byte G1 + 256 byte G2)
 * Output: 32 bytes (1 if pairing result is 1, 0 otherwise) */
int ethjet_bls_pairing(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* MAP_FP_TO_G1 (0x10): Map field element to G1
 * Input: 64 bytes (Fp element, 16 byte padding + 48 byte value)
 * Output: 128 bytes (G1 point) */
int ethjet_bls_map_fp_to_g1(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

/* MAP_FP2_TO_G2 (0x11): Map Fp2 element to G2
 * Input: 128 bytes (Fp2 element = c0(64) || c1(64))
 * Output: 256 bytes (G2 point) */
int ethjet_bls_map_fp2_to_g2(uint8_t *in, size_t in_size, uint8_t *out, size_t out_size);

#endif /* ETHJET_BLS_H */
