#ifndef LIBETHJET_KZG_H
#define LIBETHJET_KZG_H

#include <stdint.h>
#include <stddef.h>

/* Initialize the KZG trusted setup. Must be called before using ethjet_point_evaluation.
 * Returns 1 on success, 0 on failure. */
int ethjet_kzg_init(void);

/* Free the KZG trusted setup resources. */
void ethjet_kzg_free(void);

/* Point evaluation precompile (EIP-4844 / 0x0A)
 * Input: 192 bytes - versioned_hash(32) || z(32) || y(32) || commitment(48) || proof(48)
 * Output: 64 bytes - FIELD_ELEMENTS_PER_BLOB(32) || BLS_MODULUS(32)
 * Returns 1 on success, 0 on failure (invalid proof or input) */
int ethjet_point_evaluation(uint8_t *in, size_t in_size,
                           uint8_t *out, size_t out_size);

#endif
