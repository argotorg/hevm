#!/bin/bash
set -eux -o pipefail

## The following script builds and installs c-kzg to ~/.local/lib

INSTALL_VERSION=2.1.5

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

PREFIX="$HOME/.local"
curl -LO "https://github.com/ethereum/c-kzg-4844/archive/v$INSTALL_VERSION.zip"
unzip "v$INSTALL_VERSION.zip" && rm "v$INSTALL_VERSION.zip"
cd "c-kzg-4844-$INSTALL_VERSION/src"

# Compiler flags matching flake.nix
CFLAGS="-O2 -fPIC -Wno-implicit-function-declaration -Wno-gnu-folding-constant"
CFLAGS="$CFLAGS -I$PREFIX/include -I. -Icommon -Ieip4844 -Ieip7594 -Isetup"

# Compile common files
clang $CFLAGS -c common/alloc.c -o alloc.o
clang $CFLAGS -c common/bytes.c -o bytes.o
clang $CFLAGS -c common/ec.c -o ec.o
clang $CFLAGS -c common/fr.c -o fr.o
clang $CFLAGS -c common/lincomb.c -o lincomb.o
clang $CFLAGS -c common/utils.c -o utils.o

# Compile setup files
clang $CFLAGS -c setup/setup.c -o setup.o

# Compile eip4844 files
clang $CFLAGS -c eip4844/eip4844.c -o eip4844.o
clang $CFLAGS -c eip4844/blob.c -o blob.o

# Compile eip7594 files
clang $CFLAGS -c eip7594/eip7594.c -o eip7594.o
clang $CFLAGS -c eip7594/cell.c -o cell.o
clang $CFLAGS -c eip7594/fft.c -o fft.o
clang $CFLAGS -c eip7594/fk20.c -o fk20.o
clang $CFLAGS -c eip7594/poly.c -o poly.o
clang $CFLAGS -c eip7594/recovery.c -o recovery.o

# Create static library
ar rcs libckzg.a alloc.o bytes.o ec.o fr.o lincomb.o utils.o \
    setup.o eip4844.o blob.o eip7594.o cell.o fft.o fk20.o poly.o recovery.o

# Install library and headers
mkdir -p "$PREFIX/lib" "$PREFIX/include" "$PREFIX/share"
cp libckzg.a "$PREFIX/lib/"
cp ckzg.h "$PREFIX/include/"
cp -r common "$PREFIX/include/"
cp -r eip4844 "$PREFIX/include/"
cp -r eip7594 "$PREFIX/include/"
cp -r setup "$PREFIX/include/"
cp trusted_setup.txt "$PREFIX/share/"
