import sha3
import re
from web3 import Web3
from ethereum_data import *
import helper
"""
INITIALIZATION
"""

ETHERSCAN_API = None

"""
SIMULATION ATOMS
"""
GLOBAL_STATE= {
    "currentGas": "1000",
    "pc": 0             # int
}

STACK = []              # all int in str format
# DONT forget to convert memeort to growing list
MEMORY = helper.GrowingList()             # Each element is 8 bit(1 byte) , 2 hex value  (LIKE ab not like 0xab)
next_mem_loc = 0

STORAGE = {}            # str(int) --> str(int)

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
    "currentNumber": "0x00",
    "currentTimestamp": "0x00"
  },
  "exec": {
    "data": "0xff",
    "calldata": "0xff",
    "gas": "0x0186a0",
    "gasPrice": "0x5af3107a4000",
    "origin": "0xcd1722f3947def4cf144679da39c4c32bdc35681",     #used
    "value": "0x0de0b6b3a7640000"
  },
  "gas": "0x013874",
  "Is": {
  	"address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",
    "balance": "0xd3c21bcecceda1000000"
  },
  "Ia": {
  	"address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",    #used
    "balance": "0xd3c21bcecceda1000000",
    "storage": {
      "0x00": "0x2222"
    }
  }
}

IH_BLOCKHASH = "0x0012"

"""
444 --> STOP
222 --> STACK UNDERFLOW
"""
def execute_opcode(opcode, FILE_OPCODES, FILE_PC_OPCODES):
    if(opcode == 'STOP'):       # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        return 444
    elif (opcode == 'ADD'):     # DONE
        if(len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = (first_arg + second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'MUL'):     # DONE
        if(len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = (first_arg * second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SUB'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = formed((first_arg - second_arg)) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'DIV'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if(second_arg != 0):
                result = (first_arg // second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SDIV'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(int(STACK.pop()))
            second_arg = to_signed(int(STACK.pop()))
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
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'MOD'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if (second_arg != 0):
                result = (first_arg % second_arg)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SMOD'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(int(STACK.pop()))
            second_arg = to_signed(int(STACK.pop()))
            result = 0
            if (second_arg != 0):
                sign = -1
                if (first_arg >= 0):
                    sign = 1
                result = formed(sign * (abs(first_arg) % abs(second_arg)))
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'ADDMOD'):  # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())
            result = 0
            if (third_arg != 0):
                result = (first_arg + second_arg) % (third_arg)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'MULMOD'):  # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())
            result = 0
            if (third_arg != 0):
                result = (first_arg * second_arg) % (third_arg)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'EXP'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = (first_arg ** second_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SIGNEXTEND'):  # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if first_arg >= 32 or first_arg < 0:
                result = second_arg
            else:
                signbit_index_from_right = 8 * first_arg + 7
                if second_arg & (1 << signbit_index_from_right):
                    result = second_arg | (2 ** 256 - (1 << signbit_index_from_right))
                else:
                    result = second_arg & ((1 << signbit_index_from_right) - 1)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'LT'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if first_arg < second_arg:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'GT'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if first_arg > second_arg:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SLT'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(int(STACK.pop()))
            second_arg = to_signed(int(STACK.pop()))
            result = 0
            if first_arg < second_arg:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'SGT'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = to_signed(int(STACK.pop()))
            second_arg = to_signed(int(STACK.pop()))
            result = 0
            if first_arg > second_arg:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'EQ'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if first_arg == second_arg:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'ISZERO'):  # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = 0
            if first_arg == 0:
                result = 1
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'AND'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg & second_arg
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'OR'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg | second_arg
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'XOR'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg ^ second_arg
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'NOT'):     # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'BYTE'):    # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = 0
            if (first_arg < 32 and first_arg >= 0):
                result = (second_arg >> (248 - (first_arg * 8))) & BYTE_BOUND_NUMBER
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'KECCAK256'):   # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            data = read_from_mem(first_arg, second_arg)
            hashed = Web3.sha3(data)
            hashed_hex = Web3.toHex(hashed)
            result = int(hashed_hex,16)
            #result = int(hashed_hex)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'ADDRESS'):     # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['Ia']['address']
        result = int(result,16)
        STACK.append(str(result))
    elif (opcode == 'BALANCE'):     # DONE
        if len(STACK) > 0:
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = ETHERSCAN_API.getBalance(str(first_arg))   ## returns str
            STACK.append(result)
        else:
            raise 222
    elif (opcode == 'ORIGIN'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['origin']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'CALLER'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES["Is"]["address"]
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'CALLVALUE'):   # DONE    XXXXXXX
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['value']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'CALLDATALOAD'):    # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            data = CONTRACT_PROPERTIES['exec']['calldata']
            result = data[(2+first_arg):(66+first_arg)]
            result = int(result,16)
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'CALLDATASIZE'):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        data = CONTRACT_PROPERTIES['exec']['calldata']
        result = (len(data)-2)/2
        STACK.append(str(result))
    elif (opcode == 'CALLDATACOPY'):    # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())

            for count in range(0, third_arg):
                MEMORY[first_arg + count] = CONTRACT_PROPERTIES['exec']['calldata'][2 + 2*(second_arg + count)] + CONTRACT_PROPERTIES['exec']['calldata'][3 + 2*(second_arg + count)]
        else:
            return 222
    elif (opcode == 'CODESIZE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1

        f = open('bin.txt', 'r')
        bin_file = f.read()
        f.close()
        index = bin_file.index('part:')
        bin_file = bin_file[index + 7:][:-1]

        result = len(bin_file)/2
        STACK.append(str(result))
    elif (opcode == 'CODECOPY'):        # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())

            f = open('bin.txt', 'r')
            bin_file = f.read()
            f.close()
            index = bin_file.index('part:')
            bin_file = bin_file[index + 7:][:-1]

            for count in range(0, third_arg):
                MEMORY[first_arg + count] = str(bin_file[2*(second_arg + count)]) + str(bin_file[2*(second_arg + count) + 1])
        else:
            return 222
    elif (opcode == 'GASPRICE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['gasPrice']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'EXTCODESIZE'):     # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = (len(ETHERSCAN_API.getCode(str(first_arg))) - 2)/2
            STACK.append(str(result))
        else:
            return 222
    elif (opcode == 'EXTCODECOPY'):     # DONE
        if (len(STACK) > 3):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())
            fourth_arg = int(STACK.pop())

            code = ETHERSCAN_API.getCode(str(first_arg))[2:]

            for count in range(0, fourth_arg):
                MEMORY[second_arg + count] = str(code[2*(third_arg + count)]) + str(code[2*(third_arg + count) + 1])
        else:
            return 222
    elif (opcode == 'BLOCKHASH'):       # NOT COMPLETE YET
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            result = IH_BLOCKHASH
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'COINBASE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['evn']['currentCoinbase']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'TIMESTAMP'):       # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['evn']['currentTimestamp']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'NUMBER'):          # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['evn']['currentNumber']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'DIFFICULTY'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['evn']['currentDifficulty']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'GASLIMIT'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['evn']['currentGasLimit']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'POP'):             # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
        else:
            return 222
    elif (opcode == 'MLOAD'):           # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())

            k = ""
            for i in range(0, 32):
                k = k + MEMORY[first_arg + i]
            result = k
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'MSTORE'):          # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())

            second_arg = hex(second_arg)[2:]

            len_arg = len(second_arg)
            if(len_arg < 64):
                dif = 64 - len_arg
                second_arg = "0"*dif + second_arg

            for i in range(0, 32):
                MEMORY[first_arg + i] = second_arg[2*i:2*i + 2]
        else:
            return 222
    elif (opcode == 'MSTORE8'):         # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = hex(int(STACK.pop()))

            MEMORY[first_arg] = str(int(second_arg, 16) & 0xFF)
        else:
            return 222
    elif (opcode == 'SLOAD'):           # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = STORAGE[first_arg]
            STACK.append(result)
        else:
            return 222
    elif (opcode == 'SSTORE'):          # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            STORAGE[first_arg] = second_arg
        else:
            return 222
    elif (opcode == 'JUMP'):            # DONE
        if (len(STACK) > 0):
            first_arg = int(STACK.pop())
            GLOBAL_STATE["pc"] = first_arg
        else:
            return 222
    elif (opcode == 'JUMPI'):           # DONE          True --> '1' , False --> '0'
        if (len(STACK) > 1):
            first_arg = int(STACK.pop())
            second_arg = STACK.pop()
            if second_arg == "1":    # "1" will represent true and "0" will be false
                GLOBAL_STATE["pc"] = first_arg
            else:
                GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        else:
            return 222
    elif (opcode == 'PC'):              # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = GLOBAL_STATE["pc"] - 1
        STACK.append(str(result))
    elif (opcode == 'MSIZE'):           # NOT COMPLETE and len cannot be true one!!!
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = len(MEMORY)
        STACK.append(result)
    elif (opcode == 'GAS'):             # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = GLOBAL_STATE['currentGas']
        STACK.append(result)
    elif (opcode == 'JUMPDEST'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
    elif (opcode.startswith('PUSH', 0)):    # DONE
        position = int(opcode[4:], 10)
        old_pc = GLOBAL_STATE["pc"]
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1 + position
        index = FILE_PC_OPCODES.index(old_pc)
        result = FILE_OPCODES[index].par
        STACK.append(str(result))
    elif (opcode.startswith("DUP", 0)):     # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        position = int(opcode[3:], 10)
        if(len(STACK) > position-1):
            first_arg = STACK[len(STACK)-position]
            STACK.append(first_arg)
        else:
            return 222
    elif (opcode.startswith("SWAP", 0)):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        position = int(opcode[4:], 10)
        if (len(STACK) > position):
            temp = STACK[len(STACK) - 1 - position]
            STACK[len(STACK) - 1 - position] = STACK[len(STACK) - 1]
            STACK[len(STACK) - 1] = temp
        else:
            return 222
    elif (opcode == 'LOG0'):                # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        STACK.pop()
        STACK.pop()
    elif (opcode == 'LOG1'):                # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        STACK.pop()
        STACK.pop()
        STACK.pop()
    elif (opcode == 'LOG2'):                # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
    elif (opcode == 'LOG3'):                # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
    elif (opcode == 'LOG4'):                # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
        STACK.pop()
    elif (opcode == 'CREATE'):      # WILL BE COMPLETED LATER
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()

            STACK.append("NONONO")
        else:
            return 222
    elif (opcode == 'CALL'):
        if (len(STACK) > 6):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            outgas = STACK.pop()
            recipient = STACK.pop()
            transfer_amount = STACK.pop()
            start_data_input = STACK.pop()
            size_data_input = STACK.pop()
            start_data_output = STACK.pop()
            size_data_ouput = STACK.pop()

            STACK.append("01")
        else:
            return 222
    elif (opcode == 'CALLCODE'):
        if (len(STACK) > 6):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            outgas = STACK.pop()
            recipient = STACK.pop()
            transfer_amount = STACK.pop()
            start_data_input = STACK.pop()
            size_data_input = STACK.pop()
            start_data_output = STACK.pop()
            size_data_ouput = STACK.pop()

            STACK.append("01")
        else:
            return 222
    elif (opcode == 'RETURN'):
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
        else:
            return 222
    elif (opcode == 'DELEGATECALL'):
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()

            STACK.append("01")
        else:
            return 222
    elif (opcode == 'CALLBLACKBOX'):
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
    elif (opcode == 'STATICCALL'):
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()

            STACK.append("01")
        else:
            return 222
    elif (opcode == 'REVERT'):
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
        else:
            return 222
    elif (opcode == 'INVALID'):
        return 111
    elif (opcode == 'SUICIDE'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
        else:
            return 222
    elif (opcode == 'SELFDESTRUCT'):
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
        else:
            return 222
    elif (opcode == 'SELFDESTRUCT'):
        return 111

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
        ret = ret + MEMORY[offset + length]
    return int(ret, 16)

def init_etherscan():
    ETHERSCAN_API = EthereumData()