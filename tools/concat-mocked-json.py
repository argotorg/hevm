#!/usr/bin/env python3
"""
Mock RPC data JSON File Concatenator. Once all RPC data has been collected via `--debug`,

./concat-mocked-json.py -i fetched_* -o total.json

can be used to concatenate all RPC JSON data into a single file that can
then be used to mock the RPC responses completely, eliminating the
need for live RPC calls.
"""

import json
import argparse
import sys
from pathlib import Path

def concatenate_json_files(input_files, output_file):
    unified_data = {
        "mockContract": {},
        "mockSlot": [],
        "mockBlock": {},
    }
    processed_files = 0

    for file_path in input_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
                print(f"Processing: {file_path}")
                if "mockContract" in data and data["mockContract"]:
                    unified_data["mockContract"].update(data["mockContract"])
                if "mockSlot" in data and data["mockSlot"]:
                    unified_data["mockSlot"].extend(data["mockSlot"])
                if "mockBlock" in data and data["mockBlock"]:
                    unified_data["mockBlock"].update(data["mockBlock"])
                processed_files += 1

        except FileNotFoundError:
            print(f"Error: File not found - {file_path}")
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in {file_path} - {e}")
        except Exception as e:
            print(f"Error processing {file_path}: {e}")

    try:
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(unified_data, f, indent=2, ensure_ascii=False)

        print(f"\nSuccessfully concatenated {processed_files} files")
        print(f"Output written to: {output_file}")
        print(f"Total contracts: {len(unified_data['mockContract'])}")
        print(f"Total storage slots: {len(unified_data['mockSlot'])}")
        print(f"Total blocks: {len(unified_data['mockBlock'])}")

    except Exception as e:
        print(f"Error writing output file: {e}")
        sys.exit(1)

def main():
    parser = argparse.ArgumentParser(description="Concatenate JSON files with MockData structure")
    parser.add_argument(
        "-i", "--input",
        nargs="+",
        required=True,
        help="Input JSON files (space separated)"
    )
    parser.add_argument(
        "-o", "--output",
        default="unified_mock_data.json",
        help="Output JSON file (default: unified_mock_data.json)"
    )
    args = parser.parse_args()
    input_files = args.input

    valid_files = []
    for file_path in input_files:
        if Path(file_path).exists():
            valid_files.append(file_path)
        else:
            print(f"Warning: File not found - {file_path}")

    if not valid_files:
        print("Error: No valid input files found")
        sys.exit(1)

    print(f"Found {len(valid_files)} valid input files")
    concatenate_json_files(valid_files, args.output)

if __name__ == "__main__":
    main()
