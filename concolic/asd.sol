pragma solidity ^0.4.26;
contract greeter {

    address public sender;
    /* main function */
    function greet(bool a, int256 b, uint256 c) returns (uint256) {
        uint256 time_stamp = now + c;
        if(time_stamp == 36) {
            if(b < 0) {
                return 3;
            }else {
                return 44;
            }
        } else {
            if(b == 22) {
                return 55;
            }else {
                return 555;
            }
        }
    }

    function greet2(address getter, int256 c){
         getter.call(bytes4(sha3("setN(uint256)")), 22);
    }
}

