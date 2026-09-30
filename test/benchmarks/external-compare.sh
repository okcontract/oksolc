#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2014-2026 The Solidity Authors.
# Copyright (C) 2026 OKcontract Pte. Ltd.

# Compare oksolc with the original solc 0.8.36 on external via-IR requests.

set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../../" && pwd)
benchmark_dir="${BENCHMARK_DIR:-${repo_root}/benchmarks}"
zig_parallel=false
zig_jobs=
reuse_requests=
bundled_requests=false
selected_projects=()
function usage {
    echo "Usage: external-compare.sh [--bundled-requests | --reuse-captured-requests DIR] [--zig-parallel] [--zig-jobs N] [--project NAME]... [<reference-solc>] [<oksolc>] [<runs>]"
}
while (( $# != 0 )); do
    case "$1" in
        --help|-h)
            usage
            exit 0
            ;;
        --bundled-requests)
            bundled_requests=true
            shift
            ;;
        --zig-parallel)
            zig_parallel=true
            shift
            ;;
        --zig-jobs)
            [[ $# -ge 2 ]] || {
                echo "--zig-jobs requires a positive integer" >&2
                exit 2
            }
            zig_parallel=true
            zig_jobs="$2"
            shift 2
            ;;
        --project)
            [[ $# -ge 2 ]] || {
                echo "--project requires a benchmark directory name" >&2
                exit 2
            }
            selected_projects+=("$2")
            shift 2
            ;;
        --reuse-captured-requests)
            [[ $# -ge 2 ]] || {
                echo "--reuse-captured-requests requires a directory" >&2
                exit 2
            }
            reuse_requests="$2"
            shift 2
            ;;
        --*)
            echo "unknown option: $1" >&2
            usage >&2
            exit 2
            ;;
        *)
            break
            ;;
    esac
done

report_dir="${BENCHMARK_REPORT_DIR:-${repo_root}/build/benchmarks/external}"

if (( $# > 3 )); then
    usage >&2
    exit 2
fi
if $bundled_requests && [[ -n $reuse_requests ]]; then
    echo "--bundled-requests and --reuse-captured-requests cannot be combined" >&2
    exit 2
fi

reference_input="${1:-solc}"
zig_input="${2:-${repo_root}/zig-out/bin/oksolc}"
runs="${3:-3}"
warmups="${BENCHMARK_WARMUPS:-1}"

if [[ ! $runs =~ ^[1-9][0-9]*$ ]]; then
    echo "runs must be a positive integer" >&2
    exit 2
fi
if [[ ! $warmups =~ ^[0-9]+$ ]]; then
    echo "benchmark warmups must be a nonnegative integer" >&2
    exit 2
fi
if [[ -n $zig_jobs && ! $zig_jobs =~ ^[1-9][0-9]*$ ]]; then
    echo "zig jobs must be a positive integer" >&2
    exit 2
fi

function resolve_executable {
    local value="$1"
    if [[ $value == */* ]]; then
        [[ -x $value ]] || {
            echo "executable does not exist or is not executable: $value" >&2
            return 1
        }
        local directory
        directory=$(cd "$(dirname "$value")" && pwd)
        printf '%s/%s\n' "$directory" "$(basename "$value")"
    else
        command -v "$value"
    fi
}

reference_solc=$(resolve_executable "$reference_input")
zig_solc=$(resolve_executable "$zig_input")
capture_solc="${repo_root}/test/benchmarks/capture_solc.py"
compare="${repo_root}/test/benchmarks/compare.py"

if $bundled_requests; then
    command -v zstd >/dev/null
elif [[ -z $reuse_requests ]]; then
    command -v forge >/dev/null
    [[ -x $capture_solc ]] || {
        echo "capture wrapper is not executable: $capture_solc" >&2
        exit 1
    }
fi

benchmarks=(
    uniswap-v4-2022-06-16
    openzeppelin-5.6.1
    openzeppelin-5.0.2
    openzeppelin-4.9.0
    liquity-2024-10-30
    openzeppelin-4.7.0
    openzeppelin-4.8.0
    uniswap-v4-2024-06-06
    eigenlayer-0.3.0
    sablier-v2-1.2.0
    seaport-1.6
    farcaster-3.1.0
    pendle-v2-2026-09-16
    solady-0.1.26
)
if (( ${#selected_projects[@]} != 0 )); then
    for selected in "${selected_projects[@]}"; do
        known=false
        for project in "${benchmarks[@]}"; do
            [[ $selected != "$project" ]] || known=true
        done
        if ! $known; then
            echo "unknown external benchmark project: $selected" >&2
            exit 2
        fi
    done
    benchmarks=("${selected_projects[@]}")
fi

if ! $bundled_requests && [[ -z $reuse_requests ]]; then
    missing=()
    for project in "${benchmarks[@]}"; do
        [[ -d ${benchmark_dir}/${project} ]] || missing+=("$project")
    done
    if (( ${#missing[@]} != 0 )); then
        printf 'external benchmark projects are missing from %s:\n' "$benchmark_dir" >&2
        printf '  %s\n' "${missing[@]}" >&2
        echo "run test/benchmarks/external-setup.sh first" >&2
        exit 1
    fi
fi

mkdir -p "$report_dir"
report_dir=$(cd "$report_dir" && pwd)
scratch_dir=$(mktemp -d "${TMPDIR:-/tmp}/oksolc-external.XXXXXX")
function cleanup {
    rm -r -- "$scratch_dir"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

for project in "${benchmarks[@]}"; do
    project_dir="${benchmark_dir}/${project}"
    project_scratch="${scratch_dir}/${project}"
    if $bundled_requests; then
        capture_dir="${project_scratch}/requests"
        mkdir -p "$capture_dir"
        zstd -q -d -c "${repo_root}/test/benchmarks/external-requests/${project}.json.zst" \
            > "${capture_dir}/${project}.json"
        printf 'Replaying bundled request: %s\n' "$project"
    elif [[ -n $reuse_requests ]]; then
        capture_dir="${reuse_requests}/${project}/requests"
        [[ -d $capture_dir ]] || {
            echo "captured request directory is missing: $capture_dir" >&2
            exit 1
        }
        printf 'Reusing %-26s %s\n' "$project" "$capture_dir"
    else
        # Retain requests for exact replay without Forge or project checkouts.
        capture_dir="${report_dir}/${project}/requests"
        if [[ -d $capture_dir ]]; then
            echo "capture directory already exists: $capture_dir; reuse it or choose a new BENCHMARK_REPORT_DIR" >&2
            exit 1
        fi
        mkdir -p "$capture_dir"
        mkdir -p "$project_scratch"
        printf 'Capturing %-24s ... ' "$project"
        if env \
            SOLC_REFERENCE="$reference_solc" \
            SOLC_CAPTURE_DIR="$capture_dir" \
            FOUNDRY_SOLC="$capture_solc" \
            forge build \
                --root "$project_dir" \
                --use "$capture_solc" \
                --optimize \
                --via-ir \
                --offline \
                --no-cache \
                --use-literal-content \
                --out "${project_scratch}/out" \
                --cache-path "${project_scratch}/cache" \
                >"${project_scratch}/forge.stdout" \
                2>"${project_scratch}/forge.stderr"
        then
            echo "done"
        else
            echo "Forge reported a compiler failure; comparing the captured failure path"
        fi
    fi

    request_args=()
    while IFS= read -r request_path; do
        request_args+=(--standard-json "$request_path")
    done < <(find "$capture_dir" -type f -name '*.json' -print | sort)

    if (( ${#request_args[@]} == 0 )); then
        echo "Forge did not issue a Standard JSON request for $project" >&2
        [[ -f ${project_scratch}/forge.stderr ]] && sed -n '1,120p' "${project_scratch}/forge.stderr" >&2
        exit 1
    fi

    compare_mode=()
    if $zig_parallel; then
        compare_mode+=(--zig-parallel)
    fi
    if [[ -n $zig_jobs ]]; then
        compare_mode+=(--zig-jobs "$zig_jobs")
    fi

    python3 "$compare" \
        ${compare_mode[@]+"${compare_mode[@]}"} \
        --reference-solc "$reference_solc" \
        --zig-solc "$zig_solc" \
        --runs "$runs" \
        --warmups "$warmups" \
        --aggregate "$project" \
        --allow-compiler-errors \
        --output "${report_dir}/${project}.json" \
        --summary-output "${report_dir}/${project}-summary.json" \
        "${request_args[@]}"
done

printf 'External benchmark reports: %s\n' "$report_dir"
