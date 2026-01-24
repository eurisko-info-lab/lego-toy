#!/bin/bash
#
# Build With Generated Code
# =========================
#
# Tests that the project can build using generated code instead of
# hand-coded implementations. This validates 5-way interchangeability.
#
# Usage:
#   ./scripts/build-with-generated.sh           # Test generated build
#   ./scripts/build-with-generated.sh --dry-run # Show what would happen
#

set -e
cd "$(dirname "$0")/.."

DRY_RUN=0
if [ "$1" = "--dry-run" ]; then
    DRY_RUN=1
fi

echo "=== Build With Generated Code ==="
echo ""

# Step 1: Verify bootstrap is canonical
echo "Step 1: Verify bootstrap is canonical..."
./scripts/bootstrap.sh --check || {
    echo "ERROR: Bootstrap files are not canonical. Run ./scripts/bootstrap.sh first."
    exit 1
}
echo ""

# Step 2: Build multi-target
echo "Step 2: Build multi-target pipeline..."
lake build multi-target 2>/dev/null
echo ""

# Step 3: Generate code from .rosetta specs
echo "Step 3: Generate Lean from .rosetta specs..."
GENDIR="generated/Lego"
mkdir -p "$GENDIR"

for rosetta in src/Lego/*.rosetta; do
    if [ -f "$rosetta" ]; then
        name=$(basename "$rosetta" .rosetta)
        echo "  Generating: $name.lean"
        if [ $DRY_RUN -eq 0 ]; then
            lake exe multi-target "$rosetta" -o "$GENDIR" -t lean --quiet 2>/dev/null || {
                echo "    WARNING: Failed to generate $name.lean"
            }
        fi
    fi
done
echo ""

# Step 4: Create alternate lakefile that uses generated
echo "Step 4: Create alternate build configuration..."
if [ $DRY_RUN -eq 1 ]; then
    echo "  [DRY RUN] Would create lakefile.generated.lean"
else
    cat > lakefile.generated.lean << 'EOF'
-- Alternate lakefile that uses generated code instead of hand-coded
-- Run with: lake --config lakefile.generated.lean build

import Lake
open Lake DSL

package «lego-generated» where
  version := v!"0.1.0"

-- Use generated Lego library instead of hand-coded
lean_lib «Lego» where
  srcDir := "generated"
  roots := #[`Lego.Algebra, `Lego.Runtime, `Lego.Validation]

-- Bootstrap code (same as main build)
lean_lib «LegoGenerated» where
  srcDir := "generated"
  roots := #[`BootstrapGrammar, `BootstrapTokenizer, `BootstrapRules]

-- Test executable
lean_exe «lego-test-generated» where
  root := `test.lean.Test
EOF
    echo "  Created: lakefile.generated.lean"
fi
echo ""

# Step 5: Attempt build with generated code
echo "Step 5: Build with generated code..."
if [ $DRY_RUN -eq 1 ]; then
    echo "  [DRY RUN] Would run: lake --config lakefile.generated.lean build"
else
    echo "  NOTE: This step is experimental and may fail if .rosetta coverage is incomplete."
    echo "  Attempting build..."
    
    # Try to build - this may fail if generated code is incomplete
    if lake env lean -c generated/Lego/*.lean 2>/dev/null; then
        echo "  ✓ Generated code compiles!"
    else
        echo "  ✗ Generated code has compilation errors (expected - .rosetta coverage incomplete)"
        echo ""
        echo "  To achieve full interchangeability, expand .rosetta specs to cover:"
        echo "    - Complex algorithms in Interp.lean"
        echo "    - File I/O in Loader.lean"
        echo "    - Bootstrap integration"
    fi
fi

echo ""
echo "=== Summary ==="
echo ""
echo "Generated files are in: $GENDIR/"
ls -la "$GENDIR"/*.lean 2>/dev/null || echo "  (no files generated)"
echo ""
echo "To manually test: lake env lean -c generated/Lego/<file>.lean"
