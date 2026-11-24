/* ethjet for the wasm build, which has neither libsecp256k1 nor libff: ECRECOVER is
   done in Haskell, and EVM.Precompiled.supported keeps the BN254 ops from reaching here */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "blake2.h"

struct ethjet_context { int unused; };

struct ethjet_context *
ethjet_init ()
{
  return malloc (sizeof (struct ethjet_context));
}

void
ethjet_free (struct ethjet_context *ctx)
{
  free (ctx);
}

static int
ethjet_blake2 (uint8_t *in, size_t in_size, uint8_t *out, size_t out_size)
{
  if (in_size != 213 || out_size != 64)
    return 0;

  uint32_t rounds = in[0] << 24 | in[1] << 16 | in[2] << 8 | in[3];
  unsigned char f = in[212];
  uint64_t *h = (uint64_t *)&in[4];
  uint64_t *m = (uint64_t *)&in[68];
  uint64_t *t = (uint64_t *)&in[196];

  blake2b_compress (h, m, t, f, rounds);

  memcpy (out, h, out_size);

  return 1;
}

int
ethjet (struct ethjet_context *ctx, int op,
        uint8_t *in, size_t in_size,
        uint8_t *out, size_t out_size)
{
  (void) ctx;
  if (op == 9)
    return ethjet_blake2 (in, in_size, out, out_size);
  return 0;
}
