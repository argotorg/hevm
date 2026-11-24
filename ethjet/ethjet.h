#ifndef LIBETHJET_H
#define LIBETHJET_H

#include <stddef.h>
#include <stdint.h>

enum ethjet_operation
  {
    ETHJET_ECADD = 6,
    ETHJET_ECMUL = 7,
    ETHJET_ECPAIRING = 8,
    ETHJET_BLAKE2 = 9,
    ETHJET_EXAMPLE = 0xdeadbeef,
  };

int ethjet (enum ethjet_operation op,
            uint8_t *in, size_t in_size,
            uint8_t *out, size_t out_size);

#endif
