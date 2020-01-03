pragma solidity ^0.4.26;
contract greeter {


    mapping (address => uint) public balances;
    uint public MinDeposit = 1 ether;
    bool lock_send = false;

    function Deposit() public payable {
        if(msg.value >= MinDeposit) {
            balances[msg.sender]+=msg.value;
        }
    }

    function CashOut_1(uint amount) payable{
        require(amount != 0 && balances[msg.sender] >= amount);

        uint current_balance = balances[msg.sender];
        balances[msg.sender] = 0;

        msg.sender.transfer(amount);
        balances[msg.sender] = current_balance - amount;
    }
/*
    function CashOut_2(uint amount) payable {
        require(!lock_send);
        lock_send = true;

        require(balances[msg.sender] >= amount);
        msg.sender.transfer(amount);
        balances[msg.sender] -= amount;

        lock_send = false;
    }
*/

    /*
    uint256 prize = 50;
    function opp(address getter, int256 solution) {
        if(prize == 44) {
            getter.send(10);
        }else {
            getter.send(10);
        }

    }

    function block_number(address getter, uint256 c){

        uint256 temp = block.number;  // block.number is the BLOCK NUMBER OF THE CONTRACT
        if(temp > 100000) {
             getter.call.value(123).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(321).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function timestamp(address getter, uint256 c){
        uint256 temp = now + c;  // Now is the timestamp of the contract
        if(temp > 100000) {
             getter.call.value(20).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }else {
             getter.call.value(10).gas(10)(abi.encodeWithSignature("register(string)", "MyName"));
        }
    }

    function coverage(int256 par1, int256 par2, int256 par3)returns (uint256){
        if(par1 == 12) {
            if(par1 < 10) {
                return 0;
            }else if(par1 - par2 == 4) {
                return 1;
            }else if(par1 + par2 >= 44) {
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
    */
}

