#!/bin/bash
# scaling.sh — Per-proof scaling experiment for eo2lp
#
# For each .eo proof file, measures:
#   - eo2lp encode time (translation to .lp)
#   - lambdapi check time (type-checking + SR)
#   - ethos check time (reference checker)
#   - proof size (lines, bytes)
#
# Outputs a CSV and prints progress to the terminal.
#
# Usage:
#   ./scripts/scaling.sh [OPTIONS] <proof-file-or-dir> [<proof-file-or-dir> ...]
#
# Examples:
#   ./scripts/scaling.sh proofs/QF_UF/eq_diamond/eq_diamond1.eo
#   ./scripts/scaling.sh proofs/QF_UF/QG-classification/iso_icl*.eo
#   ./scripts/scaling.sh --timeout 60 --csv results.csv proofs/QF_UF/

set -euo pipefail
export LC_NUMERIC=C

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

TIMEOUT=30
CSV_FILE="scaling_results.csv"
CPC_DIR="./cpc"
ETHOS_CPC="${ETHOS_CPC:-$HOME/prog/cvc5/proofs/eo/cpc/Cpc.eo}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

INPUTS=()

print_usage() {
  cat <<EOF
Usage: $(basename "$0") [OPTIONS] <proof-files-or-dirs...>

Per-proof scaling experiment: measures encode, check, and ethos times.

Options:
  --timeout N        Timeout for encode and check phases (default: $TIMEOUT)
  --csv FILE         Output CSV file (default: $CSV_FILE)
  --cpc DIR          CPC directory for eo2lp (default: $CPC_DIR)
  --ethos-cpc FILE   CPC file for ethos --include (default: $ETHOS_CPC)
  -h, --help         Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --timeout)    TIMEOUT="$2"; shift 2 ;;
    --csv)        CSV_FILE="$2"; shift 2 ;;
    --cpc)        CPC_DIR="$2"; shift 2 ;;
    --ethos-cpc)  ETHOS_CPC="$2"; shift 2 ;;
    -h|--help)    print_usage; exit 0 ;;
    -*)           echo "Unknown option: $1" >&2; print_usage; exit 1 ;;
    *)            INPUTS+=("$1"); shift ;;
  esac
done

if [[ ${#INPUTS[@]} -eq 0 ]]; then
  echo "Error: specify at least one proof file or directory" >&2
  print_usage
  exit 1
fi

# ---------------------------------------------------------------------------
# Collect proof files
# ---------------------------------------------------------------------------

PROOFS=()
for input in "${INPUTS[@]}"; do
  if [[ -f "$input" ]]; then
    PROOFS+=("$(realpath "$input")")
  elif [[ -d "$input" ]]; then
    while IFS= read -r f; do
      PROOFS+=("$f")
    done < <(find "$(realpath "$input")" -name '*.eo' -type f | sort)
  else
    echo "Warning: $input not found, skipping" >&2
  fi
done

N=${#PROOFS[@]}
if [[ "$N" -eq 0 ]]; then
  echo "No .eo files found." >&2
  exit 1
fi

# Sort by size
mapfile -t PROOFS < <(
  for f in "${PROOFS[@]}"; do
    printf "%d %s\n" "$(wc -l < "$f")" "$f"
  done | sort -n | awk '{print $2}'
)

# ---------------------------------------------------------------------------
# Colors
# ---------------------------------------------------------------------------

if [[ -t 1 ]]; then
  RED=$'\033[31m'; GREEN=$'\033[32m'; YELLOW=$'\033[33m'
  DIM=$'\033[2m'; BOLD=$'\033[1m'; RESET=$'\033[0m'
else
  RED='' GREEN='' YELLOW='' DIM='' BOLD='' RESET=''
fi

# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------

echo -n "${DIM}building eo2lp...${RESET} "
(cd "$PROJECT_DIR" && dune build 2>/dev/null)
echo "${GREEN}ok${RESET}"

# ---------------------------------------------------------------------------
# Init CSV
# ---------------------------------------------------------------------------

echo "file,eo_lines,eo_bytes,n_assume,n_step,n_define,n_declare,encode_ms,check_ms,ethos_ms,status,error" > "$CSV_FILE"

# ---------------------------------------------------------------------------
# Header
# ---------------------------------------------------------------------------

echo
printf "${BOLD}scaling experiment${RESET}  ${DIM}%d proofs, %ds timeout${RESET}\n" "$N" "$TIMEOUT"
printf "${DIM}%-30s %6s %5s/%5s/%4s %8s %8s %8s  %s${RESET}\n" "proof" "lines" "step" "def" "asm" "encode" "check" "ethos" "status"
printf "${DIM}%-30s %6s %5s/%5s/%4s %8s %8s %8s  %s${RESET}\n" \
  "$(printf '%0.s─' {1..30})" "──────" "─────" "─────" "────" "────────" "────────" "────────" "──────"

# ---------------------------------------------------------------------------
# Run each proof
# ---------------------------------------------------------------------------

pass=0
fail=0
tmo=0

for proof in "${PROOFS[@]}"; do
  name=$(basename "$proof" .eo)
  lines=$(wc -l < "$proof")
  bytes=$(wc -c < "$proof")
  n_assume=$(grep -c "^(assume " "$proof" || true)
  n_step=$(grep -c "^(step " "$proof" || true)
  n_define=$(grep -c "^(define " "$proof" || true)
  n_declare=$(grep -c "^(declare-const " "$proof" || true)

  # --- eo2lp encode + lambdapi check ---
  out=$(cd "$PROJECT_DIR" && dune exec eo2lp -- \
    -d "$CPC_DIR" \
    --proofs "$proof" \
    --check \
    --bench \
    --timeout "$TIMEOUT" \
    --check-timeout "$TIMEOUT" \
    --no-color \
    -v error 2>&1) || true

  enc_ms=$(echo "$out" | sed -n 's/.*BENCH [^ ]* encode [^ ]* \([0-9]*\).*/\1/p')
  chk_ms=$(echo "$out" | sed -n 's/.*BENCH [^ ]* check [^ ]* \([0-9]*\).*/\1/p')
  chk_stat=$(echo "$out" | sed -n 's/.*BENCH [^ ]* check \([^ ]*\) .*/\1/p')

  # Extract error if any
  error=""
  if [[ "$chk_stat" == "error" ]]; then
    error=$(echo "$out" | grep -oP '\[\d+:\d+-\d+:\d+\].*' | head -1 | tr ',' ';')
  fi

  # --- ethos check ---
  ethos_ms=""
  if [[ -f "$ETHOS_CPC" ]]; then
    t0=$(date +%s%N)
    ethos_out=$(timeout "$TIMEOUT" ethos --include="$ETHOS_CPC" "$proof" 2>&1) || true
    t1=$(date +%s%N)
    ethos_ms=$(( (t1 - t0) / 1000000 ))
    if [[ "$ethos_out" != "correct" ]]; then
      ethos_ms="${ethos_ms}!"
    fi
  fi

  # --- Determine status ---
  status="ok"
  if [[ -z "$chk_stat" ]]; then
    status="encode_fail"
  elif [[ "$chk_stat" == "error" ]]; then
    # Distinguish timeout from other errors
    if [[ "$chk_ms" -ge $(( TIMEOUT * 1000 - 100 )) ]] 2>/dev/null; then
      status="timeout"
    else
      status="check_fail"
    fi
  fi

  # --- CSV ---
  echo "${name},${lines},${bytes},${n_assume},${n_step},${n_define},${n_declare},${enc_ms:-},${chk_ms:-},${ethos_ms:-},${status},${error}" >> "$CSV_FILE"

  # --- Terminal output ---
  case "$status" in
    ok)
      color="$GREEN"
      ((pass++)) || true
      ;;
    timeout)
      color="$YELLOW"
      ((tmo++)) || true
      ;;
    *)
      color="$RED"
      ((fail++)) || true
      ;;
  esac

  fmt_enc="${enc_ms:--}ms"
  fmt_chk="${chk_ms:--}ms"
  fmt_ethos="${ethos_ms:--}ms"

  printf "%-30s %6d %5d/%5d/%4d %8s %8s %8s  ${color}%s${RESET}\n" \
    "$name" "$lines" "$n_step" "$n_define" "$n_assume" "$fmt_enc" "$fmt_chk" "$fmt_ethos" "$status"
done

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

echo
printf "${BOLD}%d${RESET} pass" "$pass"
[[ "$fail" -gt 0 ]] && printf "  ${RED}%d fail${RESET}" "$fail"
[[ "$tmo"  -gt 0 ]] && printf "  ${YELLOW}%d timeout${RESET}" "$tmo"
printf "  ${DIM}(%d total)${RESET}\n" "$N"
echo "${DIM}Results: $CSV_FILE${RESET}"
