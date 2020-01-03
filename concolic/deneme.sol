pragma solidity ^0.4.26;
contract greeter {


    int256 owner;
    uint256 price;
    int256 wallet;
    uint256 prize_money;
    bool status ;

    function opp(address getter) {
        uint256 kel = 22222;
        if(owner == 44) {
            getter.send(12);
            //getter.call.value(kel + 2).gas(price)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
            getter.send(13);
            //getter.call.value(kel + 2).gas(price)(abi.encodeWithSignature("register(string)", "MyName"));
        }

    }

    function setPrize(int256 np, uint256 pp) {
        owner = np;
        //price = pp;
    }
/*



    function deneme(int256 den)returns (uint256){
        if(owner == 33) {
            if(wallet == 55) {
                return 1;
            }
            return 2;
        }else{
            if(wallet == 66) {
                return 3;
            }
            return 4;
        }
    }
*/
}

