// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract Identity {
    function identity(uint256 x) external pure returns (uint256) {
        return x;
    }
}
