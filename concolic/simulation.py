import sha3
from web3 import Web3
from ethereum_data import *
"""
INITIALIZATION
"""

ETHERSCAN_API = None

"""
SIMULATION ATOMS
"""
GLOBAL_STATE= {}

STACK = []

MEMORY = []             # Each element is 8 bit(1 byte)
next_mem_loc = 0

STORAGE = {}

"""
USEFUL STUFFS
"""
UNSIGNED_BOUND_NUMBER = 2**256 - 1

NEGATIVE_BOUND_NUMBER = 2**256

BYTE_BOUND_NUMBER = 2**8 - 1

"""
CONTRACT PROPERTIES
"""
CONTRACT_PROPERTIES = {
  "env": {
    "currentCoinbase": "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",
    "currentDifficulty": "0x0100",
    "currentGasLimit": "0x0f4240",
    "currentNumber": "0x00"
  },
  "exec": {
    "data": "0xff",
    "calldata": "0xff",
    "gas": "0x0186a0",
    "gasPrice": "0x5af3107a4000",
    "origin": 0xcd1722f3947def4cf144679da39c4c32bdc35681,
    "value": 0x0de0b6b3a7640000
  },
  "gas": "0x013874",
  "Is": {
  	"address": 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
    "balance": "0xd3c21bcecceda1000000"
  },
  "Ia": {
  	"address": 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
    "balance": "0xd3c21bcecceda1000000",
    "storage": {
      "0x00": "0x2222"
    }
  }
}

"""
444 --> STOP
222 --> STACK UNDERFLOW
"""
def execute_opcode(opcode):
    if(opcode == 'STOP'):       # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        return 444
    elif (opcode == 'ADD'):     # DONE
        if(len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = (first_arg + second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MUL'):     # DONE
        if(len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = (first_arg * second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SUB'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = formed((first_arg - second_arg)) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'DIV'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if(second_arg != 0):
                result = (first_arg // second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SDIV'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(STACK.pop())
            second_arg = to_signed(STACK.pop())
            result = 0
            if (second_arg == 0):
                result = 0
            elif (first_arg == -2**255 and second_arg == -1):
                result = -2 ** 255
            else:
                sign = -1
                if ((first_arg // second_arg) > 0):
                    sign = 1
                result = formed(sign * (abs(first_arg) // abs(second_arg)))
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MOD'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if (second_arg != 0):
                result = (first_arg % second_arg)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SMOD'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(STACK.pop())
            second_arg = to_signed(STACK.pop())
            result = 0
            if (second_arg != 0):
                sign = -1
                if (first_arg >= 0):
                    sign = 1
                result = formed(sign * (abs(first_arg) % abs(second_arg)))
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'ADDMOD'):  # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            third_arg = STACK.pop()
            result = 0
            if (third_arg != 0):
                result = (first_arg + second_arg) % (third_arg)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MULMOD'):  # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            third_arg = STACK.pop()
            result = 0
            if (third_arg != 0):
                result = (first_arg * second_arg) % (third_arg)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'EXP'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = (first_arg ** second_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SIGNEXTEND'):  # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if first_arg >= 32 or first_arg < 0:
                result = second_arg
            else:
                signbit_index_from_right = 8 * first_arg + 7
                if second_arg & (1 << signbit_index_from_right):
                    result = second_arg | (2 ** 256 - (1 << signbit_index_from_right))
                else:
                    result = second_arg & ((1 << signbit_index_from_right) - 1)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'LT'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if first_arg < second_arg:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'GT'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if first_arg > second_arg:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SLT'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(STACK.pop())
            second_arg = to_signed(STACK.pop())
            result = 0
            if first_arg < second_arg:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SGT'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(STACK.pop())
            second_arg = to_signed(STACK.pop())
            result = 0
            if first_arg > second_arg:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'EQ'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if first_arg == second_arg:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'ISZERO'):  # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = 0
            if first_arg == 0:
                result = 1
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'AND'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = first_arg & second_arg
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'OR'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = first_arg | second_arg
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'XOR'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = first_arg ^ second_arg
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'NOT'):     # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'BYTE'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            result = 0
            if (first_arg < 32 and first_arg >= 0):
                result = (second_arg >> (248 - (first_arg * 8))) & BYTE_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'KECCAK256'):   # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            data = read_from_mem(first_arg, second_arg)
            hashed = Web3.sha3(data)
            hashed_hex = Web3.toHex(hashed)
            result = int(hashed_hex)
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'ADDRESS'):     # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['Ia']['address']
        STACK.append(int(result))
    elif (opcode == 'BALANCE'):     # DONE
        if len(STACK) > 0:
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = ETHERSCAN_API.getBalance(str(first_arg))
            STACK.append(int(result))
        else:
            raise 222
    elif (opcode == 'ORIGIN'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['origin']
        STACK.append(int(result))
    elif (opcode == 'CALLER'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES["Is"]["address"]
        STACK.append(int(result))
    elif (opcode == 'CALLVALUE'):   # DONE    XXXXXXX
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['value']
        STACK.append(int(result))
    elif (opcode == 'CALLDATALOAD'):    # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            data = CONTRACT_PROPERTIES['exec']['calldata']
            result = data[(2+first_arg):(66+first_arg)]
            STACK.append(int(result,16))
        else:
            return 222
    elif (opcode == 'CALLDATASIZE'):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        data = CONTRACT_PROPERTIES['exec']['calldata']
        result = (len(data)-2)/2
        STACK.append(result)
    elif (opcode == 'CALLDATACOPY'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'CODESIZE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'CODECOPY'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'GASPRICE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'EXTCODESIZE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'EXTCODECOPY'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'BLOCKHASH'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'COINBASE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'TIMESTAMP'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'NUMBER'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'DIFFICULTY'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'GASLIMIT'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'POP'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MLOAD'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MSTORE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MSTORE8'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SLOAD'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SSTORE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'JUMP'):
        print("asd")
    elif (opcode == 'JUMPI'):
        print("asd")
    elif (opcode == 'PC'):
        print("asd")
    elif (opcode == 'MSIZE'):
        print("asd")
    elif (opcode == 'GAS'):
        print("asd")
    elif (opcode == 'JUMPDEST'):
        print("asd")
    elif (opcode == 'PUSH1'):
        print("asd")
    elif (opcode == 'PUSH2'):
        print("asd")
    elif (opcode == 'PUSH3'):
        print("asd")
    elif (opcode == 'PUSH4'):
        print("asd")
    elif (opcode == 'PUSH5'):
        print("asd")
    elif (opcode == 'PUSH6'):
        print("asd")
    elif (opcode == 'PUSH7'):
        print("asd")
    elif (opcode == 'PUSH8'):
        print("asd")
    elif (opcode == 'PUSH9'):
        print("asd")
    elif (opcode == 'PUSH10'):
        print("asd")
    elif (opcode == 'PUSH11'):
        print("asd")
    elif (opcode == 'PUSH12'):
        print("asd")
    elif (opcode == 'PUSH13'):
        print("asd")
    elif (opcode == 'PUSH14'):
        print("asd")
    elif (opcode == 'PUSH15'):
        print("asd")
    elif (opcode == 'PUSH16'):
        print("asd")
    elif (opcode == 'PUSH17'):
        print("asd")
    elif (opcode == 'PUSH18'):
        print("asd")
    elif (opcode == 'PUSH19'):
        print("asd")
    elif (opcode == 'PUSH20'):
        print("asd")
    elif (opcode == 'PUSH21'):
        print("asd")
    elif (opcode == 'PUSH22'):
        print("asd")
    elif (opcode == 'PUSH23'):
        print("asd")
    elif (opcode == 'PUSH24'):
        print("asd")
    elif (opcode == 'PUSH25'):
        print("asd")
    elif (opcode == 'PUSH26'):
        print("asd")
    elif (opcode == 'PUSH27'):
        print("asd")
    elif (opcode == 'PUSH28'):
        print("asd")
    elif (opcode == 'PUSH29'):
        print("asd")
    elif (opcode == 'PUSH30'):
        print("asd")
    elif (opcode == 'PUSH31'):
        print("asd")
    elif (opcode == 'PUSH32'):
        print("asd")
    elif (opcode == 'DUP1'):
        print("asd")
    elif (opcode == 'DUP2'):
        print("asd")
    elif (opcode == 'DUP3'):
        print("asd")
    elif (opcode == 'DUP4'):
        print("asd")
    elif (opcode == 'DUP5'):
        print("asd")
    elif (opcode == 'DUP6'):
        print("asd")
    elif (opcode == 'DUP7'):
        print("asd")
    elif (opcode == 'DUP8'):
        print("asd")
    elif (opcode == 'DUP9'):
        print("asd")
    elif (opcode == 'DUP10'):
        print("asd")
    elif (opcode == 'DUP11'):
        print("asd")
    elif (opcode == 'DUP12'):
        print("asd")
    elif (opcode == 'DUP13'):
        print("asd")
    elif (opcode == 'DUP14'):
        print("asd")
    elif (opcode == 'DUP15'):
        print("asd")
    elif (opcode == 'DUP16'):
        print("asd")
    elif (opcode == 'SWAP1'):
        print("asd")
    elif (opcode == 'SWAP2'):
        print("asd")
    elif (opcode == 'SWAP3'):
        print("asd")
    elif (opcode == 'SWAP4'):
        print("asd")
    elif (opcode == 'SWAP5'):
        print("asd")
    elif (opcode == 'SWAP6'):
        print("asd")
    elif (opcode == 'SWAP7'):
        print("asd")
    elif (opcode == 'SWAP8'):
        print("asd")
    elif (opcode == 'SWAP9'):
        print("asd")
    elif (opcode == 'SWAP10'):
        print("asd")
    elif (opcode == 'SWAP11'):
        print("asd")
    elif (opcode == 'SWAP12'):
        print("asd")
    elif (opcode == 'SWAP13'):
        print("asd")
    elif (opcode == 'SWAP14'):
        print("asd")
    elif (opcode == 'SWAP15'):
        print("asd")
    elif (opcode == 'SWAP16'):
        print("asd")
    elif (opcode == 'LOG0'):
        print("asd")
    elif (opcode == 'LOG1'):
        print("asd")
    elif (opcode == 'LOG2'):
        print("asd")
    elif (opcode == 'LOG3'):
        print("asd")
    elif (opcode == 'LOG4'):
        print("asd")
    elif (opcode == 'CREATE'):
        print("asd")
    elif (opcode == 'CALL'):
        print("asd")
    elif (opcode == 'CALLCODE'):
        print("asd")
    elif (opcode == 'RETURN'):
        print("asd")
    elif (opcode == 'DELEGATECALL'):
        print("asd")
    elif (opcode == 'CALLBLACKBOX'):
        print("asd")
    elif (opcode == 'STATICCALL'):
        print("asd")
    elif (opcode == 'REVERT'):
        print("asd")
    elif (opcode == 'INVALID'):
        print("asd")
    elif (opcode == 'SUICIDE'):
        print("asd")
    elif (opcode == 'SELFDESTRUCT'):
        print("asd")

def formed(num):
    if(num < 0):
        return NEGATIVE_BOUND_NUMBER + num
    return num

def to_signed(num):
    if(num >= (2**255)):
        return num - (2**256)
    return num

def read_from_mem(offset, length):
    ret = ""
    for a in range(0,length):
        ret = ret + str(MEMORY[offset + length])
    return int(ret)

def init_etherscan():
    ETHERSCAN_API = EthereumData()