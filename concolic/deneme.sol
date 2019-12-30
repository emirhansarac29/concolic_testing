pragma solidity ^0.4.26;
contract greeter {

    bool status;

    function greet2(address getter, uint256 c){
        status = true;
        uint256 kol = now + c;
        if(kol > 100000) {
             getter.call.value(123).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(321).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function greet3(address getter, uint256 c){
        status = true;
        uint256 kol = now + c;
        if(kol > 100000) {
             getter.call.value(kol).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(kol).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }
}

