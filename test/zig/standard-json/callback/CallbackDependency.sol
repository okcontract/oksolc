// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.36;

contract CallbackDependency {
    function dependencyValue() public pure returns (uint256) {
        return 42;
    }
}
