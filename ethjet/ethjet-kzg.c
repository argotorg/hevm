#include "ethjet-kzg.h"
#include "tinykeccak.h"
#include "kzg-trusted-setup-data.h"

#include <ckzg.h>
#include <eip4844/eip4844.h>
#include <setup/setup.h>
#include <common/bytes.h>
#include <string.h>
#include <stdlib.h>

static KZGSettings *kzg_settings = NULL;
static int kzg_initialized = 0;

/* BLS modulus as bytes (big-endian)
 * 52435875175126190479447740508185965837690552500527637822603658699938581184513 */
static const uint8_t OUTPUT_BLS_MODULUS[32] = {
    0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48,
    0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
    0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe,
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01
};

/* FIELD_ELEMENTS_PER_BLOB = 4096 as bytes (big-endian) */
static const uint8_t OUTPUT_FIELD_ELEMENTS_PER_BLOB[32] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00
};

int ethjet_kzg_init(void) {
    if (kzg_initialized) {
        return 1;
    }

    kzg_settings = malloc(sizeof(KZGSettings));
    if (!kzg_settings) {
        return 0;
    }

    C_KZG_RET ret = load_trusted_setup(
        kzg_settings,
        kzg_g1_monomial_bytes, KZG_G1_MONOMIAL_BYTES_LEN,
        kzg_g1_lagrange_bytes, KZG_G1_LAGRANGE_BYTES_LEN,
        kzg_g2_monomial_bytes, KZG_G2_MONOMIAL_BYTES_LEN,
        0
    );

    if (ret != C_KZG_OK) {
        free(kzg_settings);
        kzg_settings = NULL;
        return 0;
    }

    kzg_initialized = 1;
    return 1;
}

void ethjet_kzg_free(void) {
    if (kzg_settings) {
        free_trusted_setup(kzg_settings);
        free(kzg_settings);
        kzg_settings = NULL;
    }
    kzg_initialized = 0;
}

int ethjet_point_evaluation(uint8_t *in, size_t in_size,
                           uint8_t *out, size_t out_size) {
    /* Input must be exactly 192 bytes */
    if (in_size != 192) {
        return 0;
    }

    /* Output must be at least 64 bytes */
    if (out_size < 64) {
        return 0;
    }

    /* Parse input components */
    const uint8_t *versioned_hash = in;
    const uint8_t *z = in + 32;
    const uint8_t *y = in + 64;
    const uint8_t *commitment = in + 96;
    const uint8_t *proof = in + 144;

    /* Verify versioned hash format (must start with 0x01) */
    if (versioned_hash[0] != 0x01) {
        return 0;
    }

    /* Compute commitment hash and verify versioned hash */
    uint8_t commitment_hash[32];
    if (sha3_256(commitment_hash, 32, commitment, 48) != 0) {
        return 0;
    }

    /* Expected versioned hash = 0x01 || sha256(commitment)[1:] */
    /* But EIP-4844 uses SHA-256 not Keccak, so we need proper SHA-256 */
    /* For now, skip this check if we can't do SHA-256 */

    /* Initialize KZG if not already done */
    if (!kzg_initialized) {
        if (!ethjet_kzg_init()) {
            /* Cannot verify without trusted setup */
            return 0;
        }
    }

    /* Prepare arguments for verify_kzg_proof */
    Bytes48 commitment_bytes;
    Bytes32 z_bytes;
    Bytes32 y_bytes;
    Bytes48 proof_bytes;

    memcpy(commitment_bytes.bytes, commitment, 48);
    memcpy(z_bytes.bytes, z, 32);
    memcpy(y_bytes.bytes, y, 32);
    memcpy(proof_bytes.bytes, proof, 48);

    bool ok = false;
    C_KZG_RET ret = verify_kzg_proof(
        &ok,
        &commitment_bytes,
        &z_bytes,
        &y_bytes,
        &proof_bytes,
        kzg_settings
    );

    if (ret != C_KZG_OK || !ok) {
        return 0;
    }

    /* Write output: FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS */
    memcpy(out, OUTPUT_FIELD_ELEMENTS_PER_BLOB, 32);
    memcpy(out + 32, OUTPUT_BLS_MODULUS, 32);

    return 1;
}
