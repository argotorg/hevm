#!/bin/bash
set -eux -o pipefail

## The following script builds and installs libff to ~/.local/lib

INSTALL_VERSION=0.2.1

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

if [ -d libff ]; then
  echo "$(pwd)/libff" already exists! Using it instead of re-cloning the repo.
else
  git clone https://github.com/scipr-lab/libff -b "v$INSTALL_VERSION" --recursive
fi
cd libff
git checkout "v$INSTALL_VERSION" && git submodule init && git submodule update

patch -p1 < ../.github/scripts/libff.patch

sed -i 's/find_library(GMP_LIBRARY gmp)/find_library(GMP_LIBRARY NAMES libgmp.a)/' CMakeLists.txt
# This ends up causing the system headers to be included with -I and
# thus they override the GHC mingw compiler ones. So this removes it
# and re-adds the include with idirafter via the toolchain file
sed -i '/INCLUDE_DIRECTORIES.*OPENSSL_INCLUDE_DIR/d' CMakeLists.txt
PREFIX="$HOME/.local"
ARGS=("-DCMAKE_INSTALL_PREFIX=$PREFIX" "-DWITH_PROCPS=OFF" "-G" "Ninja" "-DCMAKE_TOOLCHAIN_FILE=$PWD/../.github/scripts/windows-ghc-toolchain.cmake")
CXXFLAGS="-fPIC"

mkdir -p build
cd build
CXXFLAGS="$CXXFLAGS" cmake -DCMAKE_POLICY_VERSION_MINIMUM=3.5 "${ARGS[@]}" ..
cmake --build . && cmake --install .

# cmake install may not copy headers, so do it manually
# ../libff/ is the source header directory (inside the libff repo)
cp -r ../libff "$PREFIX/include/"
