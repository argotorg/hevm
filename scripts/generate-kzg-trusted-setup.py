#!/usr/bin/env python3
"""
Generate a C header file with embedded KZG trusted setup data.

Parses the trusted_setup.txt format from c-kzg-4844 and outputs byte arrays
that can be used with load_trusted_setup() instead of load_trusted_setup_file().

File format (trusted_setup.txt):
  Line 1: n1 (number of G1 points, typically 4096)
  Line 2: n2 (number of G2 points, typically 65)
  Following lines: hex-encoded bytes, whitespace separated
    - First: n1 G1 Lagrange points (48 bytes each)
    - Then: n2 G2 Monomial points (96 bytes each)
    - Finally: n1 G1 Monomial points (48 bytes each)

Usage:
  python generate-kzg-trusted-setup.py trusted_setup.txt output.h
"""

import sys
import re

G1_POINT_SIZE = 48
G2_POINT_SIZE = 96


def hex_to_bytes(hex_str):
    """Convert a hex string to a list of bytes."""
    return [int(hex_str[i:i+2], 16) for i in range(0, len(hex_str), 2)]


def parse_trusted_setup(filepath):
    """Parse trusted_setup.txt and return the three byte arrays."""
    with open(filepath, 'r') as f:
        lines = [line.strip() for line in f if line.strip()]

    # First two lines are counts
    n1 = int(lines[0])  # Number of G1 points (4096)
    n2 = int(lines[1])  # Number of G2 points (65)

    # Remaining lines are hex-encoded points (one per line)
    hex_points = lines[2:]

    # Expected number of points
    expected_points = n1 + n2 + n1  # G1 Lagrange + G2 Monomial + G1 Monomial
    if len(hex_points) != expected_points:
        raise ValueError(
            f"Expected {expected_points} points, got {len(hex_points)}. "
            f"(n1={n1}, n2={n2})"
        )

    # Parse points in order: G1 Lagrange, G2 Monomial, G1 Monomial
    offset = 0

    # G1 Lagrange points (n1 points, 48 bytes each)
    g1_lagrange = []
    for i in range(n1):
        point_bytes = hex_to_bytes(hex_points[offset + i])
        if len(point_bytes) != G1_POINT_SIZE:
            raise ValueError(
                f"G1 Lagrange point {i} has {len(point_bytes)} bytes, "
                f"expected {G1_POINT_SIZE}"
            )
        g1_lagrange.extend(point_bytes)
    offset += n1

    # G2 Monomial points (n2 points, 96 bytes each)
    g2_monomial = []
    for i in range(n2):
        point_bytes = hex_to_bytes(hex_points[offset + i])
        if len(point_bytes) != G2_POINT_SIZE:
            raise ValueError(
                f"G2 Monomial point {i} has {len(point_bytes)} bytes, "
                f"expected {G2_POINT_SIZE}"
            )
        g2_monomial.extend(point_bytes)
    offset += n2

    # G1 Monomial points (n1 points, 48 bytes each)
    g1_monomial = []
    for i in range(n1):
        point_bytes = hex_to_bytes(hex_points[offset + i])
        if len(point_bytes) != G1_POINT_SIZE:
            raise ValueError(
                f"G1 Monomial point {i} has {len(point_bytes)} bytes, "
                f"expected {G1_POINT_SIZE}"
            )
        g1_monomial.extend(point_bytes)

    return g1_monomial, g1_lagrange, g2_monomial


def format_byte_array(name, data, bytes_per_line=16):
    """Format a byte array as a C static const array."""
    lines = []
    lines.append(f"static const uint8_t {name}[] = {{")

    for i in range(0, len(data), bytes_per_line):
        chunk = data[i:i + bytes_per_line]
        hex_values = ", ".join(f"0x{b:02x}" for b in chunk)
        if i + bytes_per_line < len(data):
            lines.append(f"    {hex_values},")
        else:
            lines.append(f"    {hex_values}")

    lines.append("};")
    return "\n".join(lines)


def generate_header(g1_monomial, g1_lagrange, g2_monomial):
    """Generate the C header file content."""
    header = []

    header.append("/* Auto-generated KZG trusted setup data.")
    header.append(" * Do not edit manually - regenerate with generate-kzg-trusted-setup.py")
    header.append(" */")
    header.append("")
    header.append("#ifndef KZG_TRUSTED_SETUP_DATA_H")
    header.append("#define KZG_TRUSTED_SETUP_DATA_H")
    header.append("")
    header.append("#include <stdint.h>")
    header.append("")
    header.append(f"#define KZG_G1_MONOMIAL_BYTES_LEN {len(g1_monomial)}")
    header.append(f"#define KZG_G1_LAGRANGE_BYTES_LEN {len(g1_lagrange)}")
    header.append(f"#define KZG_G2_MONOMIAL_BYTES_LEN {len(g2_monomial)}")
    header.append("")

    header.append(format_byte_array("kzg_g1_monomial_bytes", g1_monomial))
    header.append("")
    header.append(format_byte_array("kzg_g1_lagrange_bytes", g1_lagrange))
    header.append("")
    header.append(format_byte_array("kzg_g2_monomial_bytes", g2_monomial))
    header.append("")
    header.append("#endif /* KZG_TRUSTED_SETUP_DATA_H */")

    return "\n".join(header)


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <trusted_setup.txt> <output.h>",
              file=sys.stderr)
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    print(f"Parsing {input_file}...")
    g1_monomial, g1_lagrange, g2_monomial = parse_trusted_setup(input_file)

    print(f"  G1 Monomial: {len(g1_monomial)} bytes")
    print(f"  G1 Lagrange: {len(g1_lagrange)} bytes")
    print(f"  G2 Monomial: {len(g2_monomial)} bytes")

    print(f"Generating {output_file}...")
    header_content = generate_header(g1_monomial, g1_lagrange, g2_monomial)

    with open(output_file, 'w') as f:
        f.write(header_content)
        f.write("\n")

    print("Done.")


if __name__ == "__main__":
    main()
