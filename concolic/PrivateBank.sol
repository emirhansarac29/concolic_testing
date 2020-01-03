pragma solidity ^0.4.26;

contract PrivateBank {

    // THIS IS AN EXAMPLE OF CONTRACT THAT DEMONSTRATE REENTRANCY BUG AND SOLUTIONS (Got from ContractFuzzer)

    mapping (address => uint) public balances;
    uint public MinDeposit = 1 ether;
    bool lock_send = false;

    function Deposit() public payable {
        if(msg.value >= MinDeposit) {
            balances[msg.sender]+=msg.value;
        }
    }

    /*
    function CashOut_1(uint amount) payable{
        require(amount != 0 && balances[msg.sender] >= amount);

        uint current_balance = balances[msg.sender];
        balances[msg.sender] = 0;

        msg.sender.transfer(amount);
        balances[msg.sender] = current_balance - amount;
    }

    function err_CashOut_1(uint amount) payable{
        require(amount != 0 && balances[msg.sender] >= amount);
        msg.sender.transfer(amount);
        balances[msg.sender] -= amount;
    }

    function CashOut_2(uint amount) payable {
        require(!lock_send);
        lock_send = true;

        require(balances[msg.sender] >= amount);
        msg.sender.transfer(amount);
        balances[msg.sender] -= amount;

        lock_send = false;
    }
    */
}
