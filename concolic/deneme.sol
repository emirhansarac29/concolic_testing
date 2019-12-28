pragma solidity ^0.4.26;
contract greeter {
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

    function greet2(int256 b, int256 c) returns (int256) {
        int256 kol = b*c;
        if(kol == 1000) {
            return 55;
        }else {
            return 33;
        }

    }
}

