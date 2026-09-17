// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
pragma solidity ^0.8.30;

function headerRecord(uint256 mark) returns (uint256 value) {
    assembly { value := add(mul(sload(0), 10), mark) sstore(0, value) }
}

contract ArgumentTrace {
    uint256 public trace;
    function record(uint256 mark) internal returns (uint256) {
        trace = trace * 10 + mark;
        return trace;
    }
}
contract OrderedA is ArgumentTrace {
    uint256 public a;
    constructor(uint256 value) { a = value; record(4); }
}
contract OrderedB is ArgumentTrace {
    uint256 public b;
    constructor(uint256 value) { b = value; record(5); }
}
contract OrderedInvocation is OrderedA, OrderedB {
    uint256 public initialized = trace;
    constructor() OrderedA(record(1)) OrderedB(record(2)) { record(6); }
}
contract ReversedInvocation is OrderedA, OrderedB {
    uint256 public initialized = trace;
    constructor() OrderedB(record(2)) OrderedA(record(1)) { record(6); }
}
contract OrderedHeader is OrderedA(headerRecord(1)), OrderedB(headerRecord(2)) {
    uint256 public initialized = trace;
    constructor() { record(6); }
}
abstract contract UnsuppliedMiddle is OrderedA {}
contract SuppliedByLeaf is UnsuppliedMiddle {
    constructor() OrderedA(record(3)) {}
}
contract ForwardingMiddle is OrderedA {
    constructor(uint256 value) OrderedA(record(value)) { record(7); }
}
contract ForwardingLeaf is ForwardingMiddle {
    constructor(uint256 value) ForwardingMiddle(value + 1) { record(8); }
}
contract ReferenceBase {
    uint256 public first;
    uint256 public second;
    constructor(uint256[] memory one, uint256[] memory two) {
        one[0] = 9;
        first = one[0];
        second = two[0];
    }
}
contract ReferenceLeaf is ReferenceBase {
    constructor(uint256[] memory values) ReferenceBase(values, values) {}
}
contract ConstructionOrderTest {
    function testInvocationOrder() public {
        OrderedInvocation child = new OrderedInvocation();
        assert(child.a() == 21);
        assert(child.b() == 2);
        assert(child.initialized() == 2145);
        assert(child.trace() == 21456);
    }
    function testReversedInvocationOrder() public {
        ReversedInvocation child = new ReversedInvocation();
        assert(child.a() == 21);
        assert(child.b() == 2);
        assert(child.initialized() == 2145);
        assert(child.trace() == 21456);
    }
    function testHeaderOrder() public {
        OrderedHeader child = new OrderedHeader();
        assert(child.a() == 21);
        assert(child.b() == 2);
        assert(child.initialized() == 2145);
        assert(child.trace() == 21456);
    }
    function testLeafSuppliesBase() public {
        SuppliedByLeaf child = new SuppliedByLeaf();
        assert(child.a() == 3);
        assert(child.trace() == 34);
    }
    function testForwarding() public {
        ForwardingLeaf child = new ForwardingLeaf(2);
        assert(child.a() == 3);
        assert(child.trace() == 3478);
    }
    function testReferenceForwarding() public {
        uint256[] memory values = new uint256[](1);
        values[0] = 3;
        ReferenceLeaf child = new ReferenceLeaf(values);
        assert(values[0] == 3);
        assert(child.first() == 9);
        assert(child.second() == 9);
    }
}
