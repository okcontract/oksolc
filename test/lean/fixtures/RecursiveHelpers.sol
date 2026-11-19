// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
pragma solidity =0.8.36;

// Independent Solidity reference for the recursive DSL runtime tests. This is
// not an automatically translated source or a Chainwall acceptance substitute.
contract RecursiveHelpers {
    function sumTo(uint256 n) external pure returns (uint256) { return sum(n); }
    function sum(uint256 n) internal pure returns (uint256 z) {
        uint256 keep = n;
        if (n != 0) { unchecked { z = sum(n - 1) + keep; } }
    }
    function parity(uint256 n) external pure returns (uint256, uint256) { return (even(n), odd(n)); }
    function even(uint256 n) internal pure returns (uint256) {
        if (n == 0) return 1;
        unchecked { return odd(n - 1); }
    }
    function odd(uint256 n) internal pure returns (uint256 z) {
        if (n == 0) return z;
        unchecked { return even(n - 1); }
    }
    function memorySum(uint256 n, uint256 initial) external pure returns (uint256, uint256) {
        uint256[] memory p = new uint256[](1);
        p[0] = initial;
        uint256 result = shared(n, p);
        return (result, p[0]);
    }
    function shared(uint256 n, uint256[] memory p) internal pure returns (uint256) {
        uint256 keep = n;
        unchecked {
            p[0] += n;
            if (n != 0) { uint256 child = shared(n - 1, p); p[0] = child + keep; }
        }
        return p[0];
    }
    function effects(uint256 n, uint256 mode) external returns (uint256) { return walk(n, mode); }
    function walk(uint256 n, uint256 mode) internal returns (uint256 z) {
        uint256 keep = n;
        assembly { sstore(0, add(sload(0), 1)) mstore(0, n) log1(0, 32, 7) }
        if (n == 0) {
            assembly {
                mstore(0, 57005)
                if eq(mode, 1) { revert(0, 32) }
                if eq(mode, 2) { invalid() }
                if eq(mode, 3) { return(0, 32) }
                if eq(mode, 4) { stop() }
            }
            return z;
        }
        unchecked { z = walk(n - 1, mode) + keep; }
        assembly { sstore(1, add(sload(1), keep)) }
    }
    function diverge() external pure { forever(); }
    function forever() internal pure { forever(); }
}
