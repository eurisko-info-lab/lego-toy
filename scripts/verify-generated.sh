#!/bin/bash
#
# Verify Generated Code
# =====================
#
# Compares hand-coded Lean files against their generated equivalents
# to track coverage and identify divergence.
#
# Usage:
#   ./scripts/verify-generated.sh              # Full report
#   ./scripts/verify-generated.sh --summary    # Summary only
#

set -e
cd "$(dirname "$0")/.."

SUMMARY_ONLY=0
if [ "$1" = "--summary" ]; then
    SUMMARY_ONLY=1
fi

echo "=== Verify Generated Code ==="
echo ""

# Build multi-target first
echo "Building multi-target pipeline..."
lake build multi-target 2>/dev/null

# Create temp directory for generated output
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

echo "Generating Lean from .rosetta specs..."
echo ""

# Generate Lean from all .rosetta files
for rosetta in src/Lego/*.rosetta; do
    if [ -f "$rosetta" ]; then
        name=$(basename "$rosetta" .rosetta)
        echo "  Processing: $name.rosetta"
        lake exe multi-target "$rosetta" -o "$TMPDIR" -t lean --quiet 2>/dev/null || true
    fi
done

echo ""
echo "=== Coverage Report ==="
echo ""

# Compare each hand-coded file with its generated equivalent
declare -A COVERAGE
TOTAL_HAND=0
TOTAL_GEN=0
TOTAL_MATCH=0

for handcoded in src/Lego/*.lean; do
    name=$(basename "$handcoded" .lean)
    
    # Skip re-export files
    if [ "$name" = "Lego" ]; then
        continue
    fi
    
    hand_lines=$(wc -l < "$handcoded" | tr -d ' ')
    TOTAL_HAND=$((TOTAL_HAND + hand_lines))
    
    # Look for generated equivalent
    gen_file="$TMPDIR/$name.lean"
    if [ -f "$gen_file" ]; then
        gen_lines=$(wc -l < "$gen_file" | tr -d ' ')
        TOTAL_GEN=$((TOTAL_GEN + gen_lines))
        
        # Calculate similarity (simple line count ratio)
        if [ $hand_lines -gt 0 ]; then
            ratio=$((gen_lines * 100 / hand_lines))
        else
            ratio=0
        fi
        
        if [ $SUMMARY_ONLY -eq 0 ]; then
            printf "  %-20s %4d lines (hand) vs %4d lines (gen) = %3d%%\n" \
                   "$name.lean" "$hand_lines" "$gen_lines" "$ratio"
        fi
        
        # Check if files are identical
        if diff -q "$handcoded" "$gen_file" > /dev/null 2>&1; then
            TOTAL_MATCH=$((TOTAL_MATCH + 1))
            [ $SUMMARY_ONLY -eq 0 ] && echo "    ✓ IDENTICAL"
        fi
    else
        if [ $SUMMARY_ONLY -eq 0 ]; then
            printf "  %-20s %4d lines (hand) - NO ROSETTA SPEC\n" "$name.lean" "$hand_lines"
        fi
    fi
done

echo ""
echo "=== Summary ==="
echo ""
echo "  Hand-coded total:  $TOTAL_HAND lines"
echo "  Generated total:   $TOTAL_GEN lines"
if [ $TOTAL_HAND -gt 0 ]; then
    overall=$((TOTAL_GEN * 100 / TOTAL_HAND))
    echo "  Overall coverage:  ${overall}%"
fi
echo "  Identical files:   $TOTAL_MATCH"
echo ""

# Also verify bootstrap files
echo "=== Bootstrap Verification ==="
echo ""
./scripts/bootstrap.sh --check
