pragma solidity ^0.4.26;
contract greeter {


    /* main function */
    function greet(bool a, int256 b, int256 c) returns (uint256) {

        int256 d = greet2(b,c);
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

    function greet2(int256 b, int256 c) returns (int256) {

        if(b*c == 666) {
            return 55;
        }else {
            return 33;
        }

    }



}

