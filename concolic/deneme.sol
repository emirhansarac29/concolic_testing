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
            getter.send(price);
            //getter.call.value(kel + 2).gas(price)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
            getter.send(price);
            //getter.call.value(kel + 2).gas(price)(abi.encodeWithSignature("register(string)", "MyName"));
        }

    }

    function greet3(address getter, uint256 c){
        price = c;
        uint256 kol = now + c;
        if(kol > 100000) {
             getter.call.value(kol).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(kol).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function greet2(address getter, uint256 c){

        uint256 pat= block.number;
        uint256 kol = pat + c;
        if(kol > 100000) {
             getter.call.value(123).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(321).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function setPrize(int256 np, uint256 pp) {
        owner = np;
        price = pp;
    }

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

}

