#!/bin/bash
set -eux -o pipefail

## The following script builds and installs blst to ~/.local/lib

INSTALL_VERSION=0.3.11

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

PREFIX="$HOME/.local"
curl -LO "https://github.com/supranational/blst/archive/v$INSTALL_VERSION.zip"
unzip "v$INSTALL_VERSION.zip" && rm "v$INSTALL_VERSION.zip"
cd "blst-$INSTALL_VERSION"

# Build using the provided build script
# The script auto-detects platform and uses appropriate assembly
./build.sh CFLAGS="-O2 -fPIC -D__BLST_PORTABLE__"

# Install headers and library
mkdir -p "$PREFIX/lib" "$PREFIX/include"
cp libblst.a "$PREFIX/lib/"
cp bindings/blst.h "$PREFIX/include/"
cp bindings/blst_aux.h "$PREFIX/include/"
