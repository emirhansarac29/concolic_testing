pragma solidity ^0.4.26;
contract greeter {


    /* main function */
    function greet(bool a, int256 b, int256 c) returns (uint256) {

        int256 d = b*c;
        if(a == true) {
            if(a == false) {
                return 1;
            } else {
                return 2;
            }
        } else {
            if(d == 55) {
                return 3;
            } else {
                return 4;
            }
        }

    }

}

