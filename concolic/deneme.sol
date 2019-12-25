pragma solidity ^0.4.26;
contract greeter {


    /* main function */
    function greet(bool a, uint72 b, uint256 f, int72 e, int256 ss) returns (uint256) {

        if(a == true) {
            if(ss == 12) {
                return 1;
            } else {
                return 2;
            }
        } else {
            if(ss == 55) {
                return 3;
            } else {
                return 4;
            }
        }

    }

}

