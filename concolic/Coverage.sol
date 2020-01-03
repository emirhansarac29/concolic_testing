pragma solidity ^0.4.26;
contract greeter {

    bool check;

    function coverage(int256 par1, int256 par2, int256 par3)returns (uint256){
        if(par1 == 12 || check) {
            if(par1 < 10) {
                return 0;
            }else if(par1 - par2 == 4) {
                return 1;
            }else if(par1 + par2 >= 44 || !check) {
                return 2;
            }else {
                return 3;
            }
        }else {
            if(par3*par2 == 500){
                return 4;
            }else {
                return 5;
            }
        }
    }
}

