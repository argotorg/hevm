#!/usr/bin/env bash
# Builds bitwuzla, with GMP and MPFR, and libff's BN254 for wasm32-wasi into dist-wasm/solver/prefix. Usage: [JOBS=n] wasm/build-solver.sh
set -euo pipefail

cd "$(dirname "$0")/.."
root=$PWD
sdk=${GHC_WASM:-$root/dist-wasm/toolchain}/wasi-sdk
work=$root/dist-wasm/solver
prefix=$work/prefix
jobs=${JOBS:-$(nproc)}
mkdir -p "$work/src" "$prefix"

gmp_version=6.3.0
gmp_sha256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898
mpfr_version=4.2.1
mpfr_sha256=277807353a6726978996945af13e52829e3abd7a9a5b7fb2793894e18f1fcbb2
bitwuzla_version=0.11.0
libff_version=0.2.1
libff_sha256=630010841f6992ad6e4758bb079d248eab46cfe66a4c0391c11075f3e5387b60

export CC=$sdk/bin/wasm32-wasi-clang CXX=$sdk/bin/wasm32-wasi-clang++
export AR=$sdk/bin/llvm-ar RANLIB=$sdk/bin/llvm-ranlib CC_FOR_BUILD=cc
# PIC since GHC also links hevm as a shared library; GMP raises SIGFPE on division by zero
export CFLAGS="-O2 -fPIC -D_WASI_EMULATED_SIGNAL" LIBS="-lwasi-emulated-signal"

# fetch SHA256 URL...: the first URL that works, as mirrors fail at times
fetch() {
  local sha=$1 file=$work/src/$(basename "$2")
  shift
  for url in "$@"; do
    [ -f "$file" ] || curl -fsSL --retry 3 -o "$file" "$url" || rm -f "$file"
  done
  echo "$sha  $file" | sha256sum -c --quiet
  tar -xf "$file" -C "$work/src"
}

if [ ! -f "$prefix/lib/libgmpxx.a" ]; then
  fetch $gmp_sha256 "https://ftp.gnu.org/gnu/gmp/gmp-$gmp_version.tar.xz" \
    "https://gmplib.org/download/gmp/gmp-$gmp_version.tar.xz"
  (cd "$work/src/gmp-$gmp_version" &&
    CXXFLAGS="$CFLAGS -fignore-exceptions" ./configure --host=none --build="$(./config.guess)" \
      --disable-assembly --enable-cxx --disable-shared --enable-static --prefix="$prefix" &&
    make -j"$jobs" && make install)
fi

if [ ! -f "$prefix/lib/libmpfr.a" ]; then
  fetch $mpfr_sha256 "https://ftp.gnu.org/gnu/mpfr/mpfr-$mpfr_version.tar.xz" \
    "https://www.mpfr.org/mpfr-$mpfr_version/mpfr-$mpfr_version.tar.xz"
  (cd "$work/src/mpfr-$mpfr_version" &&
    ./configure --host=wasm32-unknown-wasi --build="$(./config.guess)" \
      --with-gmp="$prefix" --disable-shared --enable-static --disable-thread-safe \
      --prefix="$prefix" &&
    make -j"$jobs" && make install)
fi

# only its BN254 curve, which hevm's precompiles use: libff's CMake would want OpenSSL.
# The CPU clock is only read for profiling, which ethjet turns off.
if [ ! -f "$prefix/lib/libff.a" ]; then
  fetch $libff_sha256 "https://github.com/scipr-lab/libff/archive/refs/tags/v$libff_version.tar.gz"
  ff=$work/src/libff-$libff_version
  mkdir -p "$work/libff-build" "$prefix/include"
  objs=()
  for src in algebra/curves/alt_bn128/alt_bn128_{g1,g2,init,pairing,pp}.cpp common/{double,profiling,utils}.cpp; do
    obj=$work/libff-build/$(basename "$src" .cpp).o
    "$CXX" -std=c++11 -O2 -fPIC -fignore-exceptions -DCURVE_ALT_BN128 -DNO_PROCPS \
      -DCLOCK_PROCESS_CPUTIME_ID=CLOCK_MONOTONIC -I"$ff" -I"$prefix/include" -c "$ff/libff/$src" -o "$obj"
    objs+=("$obj")
  done
  "$AR" rcs "$prefix/lib/libff.a" "${objs[@]}"
  (cd "$ff" && find libff \( -name '*.hpp' -o -name '*.tcc' \) -exec cp --parents {} "$prefix/include" \;)
fi

bzla=$work/src/bitwuzla
if [ ! -d "$bzla" ]; then
  git clone --depth 1 --branch "$bitwuzla_version" https://github.com/bitwuzla/bitwuzla.git "$bzla"
fi

# what CaDiCaL needs of signals, clocks and getpid
emulated="'-D_WASI_EMULATED_SIGNAL', '-D_WASI_EMULATED_PROCESS_CLOCKS', '-D_WASI_EMULATED_GETPID'"
emulated_libs="'-lwasi-emulated-signal', '-lwasi-emulated-process-clocks', '-lwasi-emulated-getpid'"

cat > "$work/cross.ini" <<EOF
[binaries]
c = '$CC'
cpp = '$CXX'
ar = '$AR'
strip = '$sdk/bin/llvm-strip'
pkg-config = 'pkg-config'

[built-in options]
c_args = ['-O2', $emulated]
cpp_args = ['-O2', '-fignore-exceptions', '-I$root/wasm/bitwuzla/include', $emulated]
cpp_link_args = [$emulated_libs]

[properties]
needs_exe_wrapper = true
pkg_config_libdir = '$prefix/lib/pkgconfig'

[host_machine]
system = 'wasi'
cpu_family = 'wasm32'
cpu = 'wasm32'
endian = 'little'
EOF

if [ ! -f "$prefix/lib/libbitwuzla.a" ]; then
  if [ ! -d "$work/bitwuzla-build" ]; then
    (cd "$bzla" &&
      meson setup "$work/bitwuzla-build" --cross-file "$work/cross.ini" \
        --prefix="$prefix" --libdir=lib --buildtype=release \
        -Ddefault_library=static -Dtesting=disabled -Dunit_testing=disabled \
        -Dmimalloc=disabled -Dextra_libdirs="$prefix/lib")
  fi
  cadical=$(sed -n 's/^directory = //p' "$bzla/subprojects/cadical.wrap")
  if ! grep -q __wasi__ "$bzla/subprojects/$cadical/src/random.cpp"; then
    patch -d "$bzla/subprojects/$cadical" -p1 < "$root/wasm/bitwuzla/cadical-wasi.patch"
  fi
  # only the libraries: bitwuzla's own binary needs threads
  ninja -C "$work/bitwuzla-build" -j "$jobs" src/libbitwuzla.a "subprojects/$cadical/src/libcadical.a"
  # meson's archives are thin: they only refer to the objects in the build directory
  for lib in src/libbitwuzla.a "subprojects/$cadical/src/libcadical.a"; do
    dir=$work/bitwuzla-build/$(dirname "$lib")
    rm -f "$prefix/lib/$(basename "$lib")"
    "$AR" rcs "$prefix/lib/$(basename "$lib")" "$dir/$(basename "$lib").p"/*.o
  done
fi

"$CXX" -std=c++20 -O2 -fPIC -fignore-exceptions \
  -I"$prefix/include" -I"$bzla/include" -I"$bzla/src" -I"$work/bitwuzla-build/src" \
  -c "$root/wasm/bitwuzla/hevm_bitwuzla.cpp" -o "$work/hevm_bitwuzla.o"
"$CC" -O2 -fPIC -I"$root/wasm/bitwuzla/include" -c "$root/wasm/bitwuzla/wasi_stubs.c" -o "$work/wasi_stubs.o"
"$AR" rcs "$prefix/lib/libhevm_bitwuzla.a" "$work/hevm_bitwuzla.o" "$work/wasi_stubs.o"
echo "built bitwuzla into $prefix"
