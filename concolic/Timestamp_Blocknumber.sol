pragma solidity ^0.4.0;

contract Timestamp_Blocknumber {

    function blockNumber(address getter, uint256 c){
        uint256 condition = block.number + c;
        if(condition > 100000) {
            getter.call.value(10).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
            getter.call.value(5).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function timestamp(address getter, uint256 c){
        uint256 condition = now + c;
        if(condition > 100000) {
             getter.call.value(10).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(5).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }
}
