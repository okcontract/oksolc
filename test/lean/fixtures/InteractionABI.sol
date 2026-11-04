// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
pragma solidity >=0.5.16 <0.9.0;

// Compiled unchanged with both historical and current Solidity ABI decoders.
contract InteractionABI {
    event Anonymous0(uint8 value) anonymous;
    function anonymous0() external { emit Anonymous0(22); }
    event Anonymous1(uint256 indexed t0, uint8 value) anonymous;
    function anonymous1() external { emit Anonymous1(11, 22); }
    event Anonymous2(uint256 indexed t0, uint256 indexed t1, uint8 value) anonymous;
    function anonymous2() external { emit Anonymous2(11, 11, 22); }
    event Anonymous3(uint256 indexed t0, uint256 indexed t1, uint256 indexed t2, uint8 value) anonymous;
    function anonymous3() external { emit Anonymous3(11, 11, 11, 22); }
    event Anonymous4(uint256 indexed t0, uint256 indexed t1, uint256 indexed t2, uint256 indexed t3, uint8 value) anonymous;
    function anonymous4() external { emit Anonymous4(11, 11, 11, 11, 22); }
    function checkedAdd(uint256 a, uint256 b) external pure returns (uint256) { return a+b; }
    function checkedSub(uint256 a, uint256 b) external pure returns (uint256) { return a-b; }
    function checkedMul(uint256 a, uint256 b) external pure returns (uint256) { return a*b; }
    function checkedDiv(uint256 a, uint256 b) external pure returns (uint256) { return a/b; }
    function checkedValue(uint8 x, address who, bool ok) external pure returns (uint8, address, bool) {
        return (x, who, ok);
    }
    function legacyValue(uint8 x, address who, bool ok) external pure returns (uint8, address, bool) {
        return (x, who, ok);
    }
    function bytesLength(bytes calldata data) external pure returns (uint256) { return data.length; }
    function memoryReturn() external pure returns (uint256, uint256) { return (22, 11); }
    function longString() external pure returns (string memory) { return "012345678901234567890123456789012"; }
}
