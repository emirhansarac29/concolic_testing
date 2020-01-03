pragma solidity ^0.4.16;

contract Mishandled_Exception {
    function callAddress(address a) payable{
        a.call();
    }
}
