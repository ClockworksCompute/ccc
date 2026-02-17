#!/bin/bash
# Bootstrap Colima + Docker CLI for CCC Linux x86-64 validation.
# Free, lightweight, no Docker Desktop license required.
# Idempotent: safe to re-run.
set -euo pipefail

echo "=== CCC Linux Runtime Bootstrap ==="

for pkg in colima docker qemu lima-additional-guestagents; do
  if brew list "$pkg" &>/dev/null; then
    echo "✓ $pkg installed"
  else
    echo "Installing $pkg..."
    brew install "$pkg"
  fi
done

# Start Colima with x86-64 if not running
if colima status 2>&1 | grep -q "Running"; then
  echo "✓ Colima already running"
else
  echo "Starting Colima (x86-64, 2 CPU, 4GB RAM)..."
  colima start --arch x86_64 --cpu 2 --memory 4 --runtime docker
fi

# Verify
echo ""
echo "=== Verify ==="
docker run --rm --platform linux/amd64 ubuntu:22.04 uname -a

echo ""
echo "=== Ready ==="
echo "Run: cd ccc && bash scripts/runtime/linux_validate.sh"
