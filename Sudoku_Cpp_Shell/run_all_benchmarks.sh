#!/usr/bin/env bash

set -euo pipefail

shell_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$shell_dir/.." && pwd)"
generator_dir="$repo_root/Sudoku_Generator"
log_dir="$shell_dir/benchmark_logs"

mkdir -p "$log_dir"

timestamp="$(date +%Y%m%d_%H%M%S)"
summary_file="$log_dir/summary_${timestamp}.txt"

configs=(
  "FC_MRV_LCV|MRV LCV FC"
  "FC_MAD_LCV|MAD LCV FC"
  "NOR_MRV_LCV|MRV LCV NOR"
  "NOR_MAD_LCV|MAD LCV NOR"
  "TOURN|TOURN"
)

difficulties=("easy" "inter" "hard")

generate_if_missing() {
  local prefix="$1"
  shift
  shopt -s nullglob
  local existing=("$generator_dir"/"${prefix}"_*.txt)
  shopt -u nullglob

  if (( ${#existing[@]} > 0 )); then
    return 0
  fi

  echo "Generating ${prefix} boards..." | tee -a "$summary_file"
  (
    cd "$generator_dir" &&
    python3 board_generator.py "$@"
  )
}

extract_metric() {
  local metric_name="$1"
  local output="$2"
  local value
  value="$(printf '%s\n' "$output" | awk -F': ' -v metric="$metric_name" '$1 == metric {print $2}' | tail -n 1)"
  if [[ -z "$value" ]]; then
    echo "0"
  else
    echo "$value"
  fi
}

count_boards() {
  local prefix="$1"
  shopt -s nullglob
  local boards=("$generator_dir"/"${prefix}"_*.txt)
  shopt -u nullglob
  echo "${#boards[@]}"
}

generate_if_missing easy easy 5 3 3 7
generate_if_missing inter inter 5 3 4 11
generate_if_missing hard hard 3 4 4 20

echo "Building solver..." | tee "$summary_file"
( cd "$shell_dir" && make ) >> "$summary_file" 2>&1

for config in "${configs[@]}"; do
  IFS='|' read -r config_name arg_string <<< "$config"
  read -r -a solver_args <<< "$arg_string"

  echo "" | tee -a "$summary_file"
  echo "=== ${config_name} ===" | tee -a "$summary_file"

  for difficulty in "${difficulties[@]}"; do
    shopt -s nullglob
    boards=("$generator_dir"/"${difficulty}"_*.txt)
    shopt -u nullglob

    if (( ${#boards[@]} == 0 )); then
      echo "${difficulty}: no boards found" | tee -a "$summary_file"
      continue
    fi

    solved=0
    total=${#boards[@]}
    total_pushes=0
    total_backtracks=0
    total_seconds=0

    for board in "${boards[@]}"; do
      board_name="$(basename "$board" .txt)"
      log_file="$log_dir/${timestamp}_${config_name}_${board_name}.log"

      start_time="$(date +%s)"
      set +e
      output="$("$shell_dir/bin/Sudoku" "${solver_args[@]}" "$board" 2>&1)"
      status=$?
      set -e
      end_time="$(date +%s)"
      elapsed=$(( end_time - start_time ))

      printf '%s\n' "$output" > "$log_file"

      if [[ $status -eq 0 ]] && ! grep -q "Failed to find a solution" <<< "$output" && ! grep -q "P:  -1" <<< "$output"; then
        solved=$(( solved + 1 ))
      fi

      pushes="$(extract_metric "Trail Pushes" "$output")"
      backtracks="$(extract_metric "Backtracks" "$output")"

      total_pushes=$(( total_pushes + pushes ))
      total_backtracks=$(( total_backtracks + backtracks ))
      total_seconds=$(( total_seconds + elapsed ))
    done

    avg_pushes=$(( total_pushes / total ))
    avg_backtracks=$(( total_backtracks / total ))

    printf '%s: solved %d/%d | avg pushes %d | avg backtracks %d | total time %ds\n' \
      "$difficulty" "$solved" "$total" "$avg_pushes" "$avg_backtracks" "$total_seconds" | tee -a "$summary_file"
  done
done

echo "" | tee -a "$summary_file"
echo "Full logs saved in: $log_dir" | tee -a "$summary_file"
echo "Summary saved in: $summary_file" | tee -a "$summary_file"
