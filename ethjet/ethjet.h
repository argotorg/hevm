#ifndef LIBETHJET_H
#define LIBETHJET_H

#include <stdint.h>

#include <secp256k1.h>

struct ethjet_context
{
  secp256k1_context *ec;
};

enum ethjet_operation
  {
    ETHJET_ECRECOVER = 1,
    ETHJET_ECADD = 6,
    ETHJET_ECMUL = 7,
    ETHJET_ECPAIRING = 8,
    ETHJET_BLAKE2 = 9,
    ETHJET_POINT_EVALUATION = 0x0A,
    ETHJET_BLS_G1ADD = 0x0B,
    ETHJET_BLS_G1MSM = 0x0C,
    ETHJET_BLS_G2ADD = 0x0D,
    ETHJET_BLS_G2MSM = 0x0E,
    ETHJET_BLS_PAIRING = 0x0F,
    ETHJET_BLS_MAP_FP_TO_G1 = 0x10,
    ETHJET_BLS_MAP_FP2_TO_G2 = 0x11,
    ETHJET_EXAMPLE = 0xdeadbeef,
  };

struct ethjet_context *
ethjet_init ();

void
ethjet_free (struct ethjet_context *ctx);

int ethjet (struct ethjet_context *ctx,
            enum ethjet_operation op,
            uint8_t *in, size_t in_size,
            uint8_t *out, size_t out_size);

#endif
