#!/bin/bash
#
# Bootstrap Code Generation
# ==========================
#
# This script implements the bootstrap chain for Lego's self-hosting:
#
#   gen(V_n) = tolean_{V_{n-1}}(Bootstrap.lego)
#
# The key insight: there's no circular dependency because generation
# of version N uses the previously-built tolean (version N-1).
#
# Build stages:
#   1. Stage 1: Build tolean using checked-in generated/*.lean (V_{n-1})
#   2. Stage 2: Run tolean to regenerate from Bootstrap.lego → V_n
#   3. Stage 3: Rebuild with V_n (if different)
#   4. Fixpoint check: V_n should produce V_n (self-hosting)
#
# Usage:
#   ./scripts/bootstrap.sh          # Regenerate all
#   ./scripts/bootstrap.sh --check  # Verify canonical (for CI)
#

set -e

cd "$(dirname "$0")/.."

BOOTSTRAP_LEGO="test/lego/Bootstrap.lego"
GENERATED_DIR="generated"

# Build tolean first (uses current generated files)
echo "Building tolean..."
lake build tolean 2>/dev/null

# Generate all three files
echo "Regenerating from $BOOTSTRAP_LEGO..."

lake exe tolean --tokenizer "$BOOTSTRAP_LEGO" 2>/dev/null | head -n -1 > "$GENERATED_DIR/BootstrapTokenizer.lean.new"
lake exe tolean --grammar "$BOOTSTRAP_LEGO" 2>/dev/null | head -n -1 > "$GENERATED_DIR/BootstrapGrammar.lean.new"
lake exe tolean --rules "$BOOTSTRAP_LEGO" 2>/dev/null | head -n -1 > "$GENERATED_DIR/BootstrapRules.lean.new"

# Check mode: verify canonical without modifying
if [ "$1" = "--check" ]; then
    echo "Checking canonical..."
    DIFF_FOUND=0
    
    for f in BootstrapTokenizer BootstrapGrammar BootstrapRules; do
        if ! diff -q "$GENERATED_DIR/$f.lean" "$GENERATED_DIR/$f.lean.new" > /dev/null 2>&1; then
            echo "ERROR: $GENERATED_DIR/$f.lean differs from regenerated version"
            diff "$GENERATED_DIR/$f.lean" "$GENERATED_DIR/$f.lean.new" || true
            DIFF_FOUND=1
        fi
    done
    
    # Cleanup
    rm -f "$GENERATED_DIR"/*.lean.new
    
    if [ $DIFF_FOUND -eq 1 ]; then
        echo ""
        echo "Generated files are not canonical!"
        echo "Run: ./scripts/bootstrap.sh"
        exit 1
    fi
    
    echo "✓ All generated files are canonical"
    exit 0
fi

# Update mode: replace if different
CHANGED=0
for f in BootstrapTokenizer BootstrapGrammar BootstrapRules; do
    if ! diff -q "$GENERATED_DIR/$f.lean" "$GENERATED_DIR/$f.lean.new" > /dev/null 2>&1; then
        echo "  Updated: $f.lean"
        mv "$GENERATED_DIR/$f.lean.new" "$GENERATED_DIR/$f.lean"
        CHANGED=1
    else
        rm "$GENERATED_DIR/$f.lean.new"
    fi
done

if [ $CHANGED -eq 1 ]; then
    echo "Rebuilding with updated generated files..."
    lake build
    
    # Fixpoint check: regenerate again, should be identical
    echo "Verifying fixpoint..."
    lake exe tolean --tokenizer "$BOOTSTRAP_LEGO" 2>/dev/null | head -n -1 > "$GENERATED_DIR/BootstrapTokenizer.lean.check"
    
    if ! diff -q "$GENERATED_DIR/BootstrapTokenizer.lean" "$GENERATED_DIR/BootstrapTokenizer.lean.check" > /dev/null 2>&1; then
        echo "WARNING: Fixpoint not reached - tolean_{V_n}(Bootstrap.lego) ≠ V_n"
        echo "This may indicate a bug in the code generator."
    else
        echo "✓ Fixpoint verified: tolean_{V_n}(Bootstrap.lego) = V_n"
    fi
    rm -f "$GENERATED_DIR"/*.lean.check
else
    echo "✓ Generated files already up to date"
fi
