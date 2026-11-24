#include "ethjet.h"
#include "blake2.h"

#include "ethjet-ff.h"

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/* 
 * The example contract at 0xdeadbeef just reverses its input.
 */
int
ethjet_example (uint8_t *in, size_t in_size,
                uint8_t *out, size_t out_size)
{
  if (out_size != in_size)
    return 0;

  for (int i = 0; i < in_size; i++)
    out[i] = in[in_size - i - 1];

  return 1;
}

int ethjet_blake2(uint8_t *in, size_t in_size,
                  uint8_t *out, size_t out_size) {
  uint32_t rounds = in[0] << 24 | in[1] << 16 | in[2] << 8 | in[3];
  unsigned char f = in[212];
  uint64_t *h = (uint64_t *)&in[4];
  uint64_t *m = (uint64_t *)&in[68];
  uint64_t *t = (uint64_t *)&in[196];

  blake2b_compress(h, m, t, f, rounds);

  memcpy(out, h, out_size);

  return 1;
}

int
ethjet (enum ethjet_operation op,
        uint8_t *in, size_t in_size,
        uint8_t *out, size_t out_size)
{
  switch (op) {
  case ETHJET_EXAMPLE:
    return ethjet_example (in, in_size, out, out_size);

  case ETHJET_ECADD:
    return ethjet_ecadd (in, in_size, out, out_size);

  case ETHJET_ECMUL:
    return ethjet_ecmul (in, in_size, out, out_size);

  case ETHJET_ECPAIRING:
    return ethjet_ecpairing (in, in_size, out, out_size);

  case ETHJET_BLAKE2:
    return ethjet_blake2 (in, in_size, out, out_size);

  default:
    return 0;
  }
}
