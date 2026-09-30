#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2014-2026 The Solidity Authors.
# Copyright (C) 2026 OKcontract Pte. Ltd.

#------------------------------------------------------------------------------
# Downloads and configures external projects used by external-compare.sh.
#
# By default the download location is the benchmarks/ dir at the repository root.
# A different directory can be provided via the BENCHMARK_DIR variable.
#
# Dependencies: Foundry, Git; Node.js/npm for old Uniswap; Node.js for Pendle.
# ------------------------------------------------------------------------------
# This file is part of solidity.
#
# solidity is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# solidity is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with solidity.  If not, see <http://www.gnu.org/licenses/>
#
# (c) 2024 solidity contributors.
#------------------------------------------------------------------------------

set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../../" && pwd)
BENCHMARK_DIR="${BENCHMARK_DIR:-${repo_root}/benchmarks}"
selected_projects=()
while (( $# != 0 )); do
    case "$1" in
        --help|-h)
            echo "Usage: external-setup.sh [--project NAME]..."
            exit 0
            ;;
        --project)
            [[ $# -ge 2 ]] || { echo "--project requires a name" >&2; exit 2; }
            selected_projects+=("$2")
            shift 2
            ;;
        *) echo "usage: $0 [--project NAME]..." >&2; exit 2 ;;
    esac
done

function sed_in_place {
    local expression="$1"
    shift

    # An explicit backup suffix is accepted by both GNU and BSD sed. Remove
    # each narrowly scoped backup immediately so an interrupted setup cannot
    # leave it looking like benchmark input.
    local path
    for path in "$@"; do
        sed -i.bak -E -e "$expression" "$path"
        rm -f -- "${path}.bak"
    done
}

function neutralize_version_pragmas {
    while IFS= read -r -d '' path; do
        sed_in_place 's/pragma solidity [^;]+;/pragma solidity *;/' "$path"
    done < <(find . -name '*.sol' -type f -print0)
}

function neutralize_via_ir {
    sed_in_place '/^via_ir[[:space:]]*=.*$/d' foundry.toml
}

function setup_foundry_project {
    local subdir="$1"
    local ref_type="$2"
    local ref="$3"
    local repo_url="$4"
    local install_function="${5:-}"

    if (( ${#selected_projects[@]} != 0 )); then
        local selected=false project
        for project in "${selected_projects[@]}"; do
            [[ ${subdir%/} != "$project" ]] || selected=true
        done
        $selected || return 0
    fi

    printf ">>> %-22s | " "$subdir"

    if [[ $ref_type != commit && $ref_type != tag ]]; then
        echo "unsupported reference type: $ref_type" >&2
        return 2
    fi

    [[ ! -e "$subdir" ]] || { printf "already exists\n"; return; }
    printf "downloading...\n\n"

    if [[ $ref_type == tag ]]; then
        git clone --depth=1 "$repo_url" "$subdir" --branch "$ref"
        pushd "$subdir"
    else
        git clone "$repo_url" "$subdir"
        pushd "$subdir"
        git checkout "$ref"
    fi
    if [[ -z $install_function ]]; then
        forge install
    else
        "$install_function"
    fi

    [[ ! -e foundry.toml ]] || neutralize_via_ir
    neutralize_version_pragmas
    popd
    echo
}

function install_liquity {
    sed_in_place 's|git@github.com:|https://github.com/|g' .gitmodules
    forge install
}

function install_old_uniswap {
    forge install
    openzeppelin_version=$(node -p \
        "require('./package.json').dependencies['@openzeppelin/contracts']")
    rm package.json
    rm yarn.lock
    npm install "@openzeppelin/contracts@${openzeppelin_version}"
}

function install_sablier {
    # NOTE: To avoid hard-coding dependency versions here we'd have to install them from npm
    # Forge installs without committing by default. Older versions exposed the
    # now-removed --no-commit spelling for that default.
    forge install \
        foundry-rs/forge-std@v1.8.2 \
        OpenZeppelin/openzeppelin-contracts@v5.0.2 \
        PaulRBerg/prb-math@v4.0.3 \
        evmcheb/solarray@a547630 \
        Vectorized/solady@v0.0.208
   cat <<EOF > remappings.txt
@openzeppelin/contracts/=lib/openzeppelin-contracts/contracts/
forge-std/=lib/forge-std/
@prb/math/=lib/prb-math/
solarray/=lib/solarray/
solady/=lib/solady/
EOF
}

function install_pendle {
    # Use the upstream package manager and immutable dependency lock; no hooks.
    YARN_ENABLE_SCRIPTS=false node .yarn/releases/yarn-4.12.0.cjs install --immutable
    # Benchmark every production contract, excluding deployment scripts/tests.
    # The shared harness supplies optimized via-IR compilation with solc 0.8.36.
    cat <<EOF > foundry.toml
[profile.default]
src = "contracts"
test = "benchmark-empty-tests"
script = "benchmark-empty-scripts"
libs = ["node_modules"]
evm_version = "cancun"
optimizer_runs = 200
EOF
}

mkdir -p "$BENCHMARK_DIR"
cd "$BENCHMARK_DIR"

setup_foundry_project openzeppelin-5.0.2/ tag v5.0.2 https://github.com/OpenZeppelin/openzeppelin-contracts
setup_foundry_project openzeppelin-4.9.0/ tag v4.9.0 https://github.com/OpenZeppelin/openzeppelin-contracts
setup_foundry_project openzeppelin-4.8.0/ tag v4.8.0 https://github.com/OpenZeppelin/openzeppelin-contracts
setup_foundry_project openzeppelin-4.7.0/ tag v4.7.0 https://github.com/OpenZeppelin/openzeppelin-contracts

setup_foundry_project liquity-2024-10-30/ commit 7f93a3f1781dfce2c4e0b6a7262deddd8a10e45b https://github.com/liquity/V2-gov install_liquity

setup_foundry_project uniswap-v4-2024-06-06/ commit ae86975b058d386c9be24e8994236f662affacdb https://github.com/Uniswap/v4-core
setup_foundry_project uniswap-v4-2022-06-16/ commit 9aeddf76e1b8646908fbcc7519c882bf458b794d https://github.com/Uniswap/v4-core install_old_uniswap

setup_foundry_project farcaster-3.1.0/ tag v3.1.0 https://github.com/farcasterxyz/contracts

# NOTE: Can't select the tag with `git clone` because a branch of the same name exists.
setup_foundry_project seaport-1.6/ commit tags/1.6 https://github.com/ProjectOpenSea/seaport

setup_foundry_project eigenlayer-0.3.0/ tag v0.3.0-holesky-rewards https://github.com/Layr-Labs/eigenlayer-contracts

setup_foundry_project sablier-v2-1.2.0/ tag v1.2.0 https://github.com/sablier-labs/v2-core install_sablier

setup_foundry_project pendle-v2-2026-09-16/ commit f24265966bb53f75d834ad705decde8e479d3a33 https://github.com/pendle-finance/pendle-core-v2-public install_pendle

for project in ${selected_projects[@]+"${selected_projects[@]}"}; do
    [[ -d "$project" ]] || { echo "unknown or missing project: $project" >&2; exit 2; }
done
