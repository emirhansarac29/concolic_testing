pragma solidity ^0.4.0;

contract TOD {      // OYENTE MISSES
    address public owner;
    bool public locked;
    uint256 prize;

    function TOD() {
        prize = 10 ether;
    }

    function setPrize(uint n_prize) {
        prize = n_prize;
    }

    function puzzle(address getter, int256 solution) {
        if(locked)
            throw;
        locked = true;
        if(isCorrect(solution)) {
            getter.transfer(prize);
        }else {
            getter.transfer(1);
        }
        locked = false;
    }

    function isCorrect(int256 solution) returns(bool){
        if((solution-1)+(solution+1) == 100) {
            return true;
        }
        return false;
    }

}
