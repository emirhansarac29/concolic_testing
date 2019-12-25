import sha3
import re
from web3 import Web3
from ethereum_data import *
from z3 import *
import helper
import six
import generator
"""
INITIALIZATION
"""
GENERATOR = generator.Generator()
ETHERSCAN_API = None

"""
SIMULATION ATOMS
"""
GLOBAL_STATE= {
    "currentGas": 1000,     # int, GAS
    "pc": 0                 # int
}

STACK = []              # all int in str format
MEMORY = helper.GrowingList()             # Each element is 8 bit(1 byte) , 2 hex value  (LIKE ab not like 0xab)
STORAGE = {}            # str(int) --> str(int)

"""
SYMBOLIC SIMULATION ATOMS
"""
SYM_REQUEST_COND = False
SYM_FIRST_CALLDATALOAD = True
SYM_STACK = []          # all kept unsigned
SYM_MEMORY = helper.GrowingList()
SYM_PATH_CONDITIONS_AND_VARS = {"path_condition" : [], "path_condition_status" : []}   #IH_BLOCKHASH
SYM_STORAGE = {}
Symbolic_Solver = Solver()
EXECUTION_PATH_TREE = {"condition" : None, 0 : None, 1 : None}
"""
USEFUL VALUES
"""
UNSIGNED_BOUND_NUMBER = 2**256 - 1

NEGATIVE_BOUND_NUMBER = 2**256

BYTE_BOUND_NUMBER = 2**8 - 1

"""
CONTRACT PROPERTIES
"""
CONTRACT_PROPERTIES = {
  "env": {
    "currentCoinbase": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",        #COINBASE
    "currentDifficulty": "0x0100",                                          #DIFFICULTY
    "currentGasLimit": "0x0f4240",                                          #GASLIMIT
    "currentNumber": "0x00",                                                #NUMBER
    "currentTimestamp": "0x00"                                              #TIMESTAMP
  },
  "exec": {
    "data": "0xff",
    "calldata": "0xfbac12f386434657432ababbaccccccdddff1231256787ac12f386434657432ababbaccccccdddfac12f386434657432ababbaccccccdddf",    #CALLDATALOAD-CALLDATASIZE-CALLDATACOPY, input data
    "gas": "0x0186a0",
    "gasPrice": "0x5af3107a4000",                               #GASPRICE
    "origin": "0xcd1722f3947def4cf144679da39c4c32bdc35681",     #origin address, sender of original transaction.
    "value": "0x0"                               #CALLVALUE, deposited value by the instruction/transaction
  },
  "gas": "0x013874",
  "Is": {
  	"address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",    #CALLER, directly responsible for this execution.
    "balance": "0xbb"                                           #CALL, their balance
  },
  "Ia": {
  	"address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",    #ORIGIN, currently executing account.
    "balance": "0xcc",                                          #CALL, my balance
    "storage": {
      "0x00": "0x2222"
    }
  },
  "IH_BLOCKHASH": "0x0012"                                      #BLOCKHASH
}

"""
444 --> STOP
222 --> STACK UNDERFLOW
"""
def symbolic_execute_opcode(opcode, FILE_OPCODES, FILE_PC_OPCODES):
    if(opcode == 'STOP'):
        return 444
    elif (opcode == 'ADD'):     # DONE
        if(len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result= 0

            if(isReal(first_arg) and is_symbolic(second_arg)):
                first_arg = to_symbolic(first_arg)
            elif(is_symbolic(first_arg) and isReal(second_arg)):
                second_arg = to_symbolic(second_arg)

            result = (first_arg + second_arg) & (UNSIGNED_BOUND_NUMBER)
            if(is_expr(result)):
                result = simplify(result)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MUL'):     # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0

            if (isReal(first_arg) and is_symbolic(second_arg)):
                first_arg = to_symbolic(first_arg)
            elif (is_symbolic(first_arg) and isReal(second_arg)):
                second_arg = to_symbolic(second_arg)

            result = (first_arg * second_arg) & (UNSIGNED_BOUND_NUMBER)
            if (is_expr(result)):
                result = simplify(result)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SUB'):     # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0

            if (isReal(first_arg) and is_symbolic(second_arg)):
                first_arg = to_symbolic(first_arg)
            elif (is_symbolic(first_arg) and isReal(second_arg)):
                second_arg = to_symbolic(second_arg)

            result = (first_arg - second_arg) & (UNSIGNED_BOUND_NUMBER)
            if (is_expr(result)):
                result = simplify(result)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'DIV'):     # DONE
        if len(SYM_STACK) > 1:
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if (second_arg == 0):
                    result = 0
                else:
                    first_arg = to_unsigned(first_arg)
                    second_arg = to_unsigned(second_arg)
                    result = (first_arg // second_arg) & (UNSIGNED_BOUND_NUMBER)
                SYM_STACK.append(result)
            else:
                if(isReal(second_arg) and second_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = UDiv(first_arg, second_arg)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SDIV'):    # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                first_arg = to_signed(first_arg)
                second_arg = to_signed(second_arg)
                if (second_arg == 0):
                    result = 0
                elif (first_arg == -2 ** 255 and second_arg == -1):
                    result = -2 ** 255
                else:
                    sign = -1
                    if ((first_arg // second_arg) >= 0):
                        sign = 1
                    result = sign * (abs(first_arg) // abs(second_arg))
                SYM_STACK.append(to_unsigned(result))
            else:
                if (isReal(second_arg) and second_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = (first_arg / second_arg)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MOD'):     # DONE
        if len(SYM_STACK) > 1:
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if (second_arg == 0):
                    result = 0
                else:
                    first_arg = to_unsigned(first_arg)
                    second_arg = to_unsigned(second_arg)
                    result = (first_arg % second_arg) & (UNSIGNED_BOUND_NUMBER)
                SYM_STACK.append(result)
            else:
                if (isReal(second_arg) and second_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = URem(first_arg, second_arg)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SMOD'):    # DONE
        if len(SYM_STACK) > 1:
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                first_arg = to_signed(first_arg)
                second_arg = to_signed(second_arg)
                if (second_arg == 0):
                    result = 0
                else:
                    sign = -1
                    if (first_arg >= 0):
                        sign = 1
                    result = sign * (abs(first_arg) % abs(second_arg))
                SYM_STACK.append(to_unsigned(result))
            else:
                if (isReal(second_arg) and second_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = SRem(first_arg, second_arg)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'ADDMOD'):  # DONE
        if (len(SYM_STACK) > 2):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            third_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg, third_arg)):
                if (third_arg == 0):
                    result = 0
                else:
                    result = ((first_arg + second_arg) % third_arg)
                SYM_STACK.append(result)
            else:
                if (isReal(third_arg) and third_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                third_arg = to_symbolic(third_arg)
                first_arg = ZeroExt(256, first_arg)
                second_arg = ZeroExt(256, second_arg)
                third_arg = ZeroExt(256, third_arg)
                result = URem((first_arg + second_arg), third_arg)
                result = Extract(255, 0, result)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MULMOD'):  # DONE
        if (len(SYM_STACK) > 2):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            third_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg, third_arg)):
                if (third_arg == 0):
                    result = 0
                else:
                    result = ((first_arg * second_arg) % third_arg)
                SYM_STACK.append(result)
            else:
                if (isReal(third_arg) and third_arg == 0):
                    SYM_STACK.append(0)
                    return
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                third_arg = to_symbolic(third_arg)
                #first_arg = ZeroExt(256, first_arg) Disabled since takes too much time
                #second_arg = ZeroExt(256, second_arg)
                #third_arg = ZeroExt(256, third_arg)
                result = URem((first_arg * second_arg), third_arg)
                #result = Extract(255, 0, result)
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'EXP'):     # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                result = (first_arg ** second_arg) & UNSIGNED_BOUND_NUMBER
                SYM_STACK.append(result)
            else:
                #first_arg = to_symbolic(first_arg)
                #second_arg = to_symbolic(second_arg)
                result = BitVec(GENERATOR.gen_arbitrary_var(), 256)
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SIGNEXTEND'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if first_arg >= 32 or first_arg < 0:
                    result = second_arg
                else:
                    signbit_index_from_right = 8 * first_arg + 7
                    if second_arg & (1 << signbit_index_from_right):
                        result = second_arg | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        result = second_arg & ((1 << signbit_index_from_right) - 1)
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                signbit_index_from_right = 8 * first_arg + 7
                z3_s_ext = lambda x: If(x & (1 << signbit_index_from_right) == 0, x & ((1 << signbit_index_from_right) - 1 ), x | (2 ** 256 - (1 << signbit_index_from_right)))
                result = z3_s_ext(second_arg)

                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'LT'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if(first_arg < second_arg):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = If(ULT(first_arg, second_arg), BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'GT'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if (first_arg > second_arg):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = If(UGT(first_arg, second_arg), BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SLT'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                first_arg = to_signed(first_arg)
                second_arg = to_signed(second_arg)
                if (first_arg < second_arg):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = If(first_arg < second_arg, BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SGT'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                first_arg = to_signed(first_arg)
                second_arg = to_signed(second_arg)
                if (first_arg > second_arg):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = If(first_arg > second_arg, BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'EQ'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg, second_arg)):
                if (first_arg == second_arg):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = If(first_arg == second_arg, BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'ISZERO'):  # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            result = 0
            if (is_all_real(first_arg)):
                if (first_arg == 0):
                    result = 1
                else:
                    result = 0
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                result = If(first_arg == 0, BitVecVal(1, 256), BitVecVal(0, 256))
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'AND'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                result = first_arg & second_arg
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = first_arg & second_arg
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'OR'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                result = first_arg | second_arg
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = first_arg | second_arg
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'XOR'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                result = first_arg ^ second_arg
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = first_arg ^ second_arg
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'NOT'):  # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            if (is_all_real(first_arg)):
                result = (~first_arg) & UNSIGNED_BOUND_NUMBER
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                result = (~first_arg) & UNSIGNED_BOUND_NUMBER
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'BYTE'):  # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                result = 0
                if (first_arg < 32 and first_arg >= 0):
                    result = (second_arg >> (248 - (first_arg * 8))) & BYTE_BOUND_NUMBER
                SYM_STACK.append(result)
            else:
                first_arg = to_symbolic(first_arg)
                second_arg = to_symbolic(second_arg)
                result = (second_arg >> (248 - (first_arg * 8))) & BYTE_BOUND_NUMBER
                if (is_symbolic(result)):
                    SYM_STACK.append(simplify(result))
                else:
                    SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'KECCAK256'):   # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if (is_all_real(first_arg, second_arg)):
                if(len(SYM_MEMORY) < first_arg + second_arg):
                    new_var_name = GENERATOR.gen_arbitrary_var()
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                    SYM_STACK.append(result)
                else:
                    data = read_from_mem_sym(first_arg, second_arg)     ## TODO COME BACK LATER
                    hashed = Web3.sha3(data)
                    hashed_hex = Web3.toHex(hashed)
                    result = int(hashed_hex,16)
                    #result = int(hashed_hex)
                    SYM_STACK.append(result)
            else:
                new_var_name = GENERATOR.gen_arbitrary_var()
                result = BitVec(new_var_name, 256)
                SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'ADDRESS'):     # DONE
        result = CONTRACT_PROPERTIES['Ia']['address']
        result = int(result,16)
        SYM_STACK.append(result)
    elif (opcode == 'BALANCE'):     # DONE
        if len(SYM_STACK) > 0:
            first_arg = SYM_STACK.pop()
            if (is_all_real(first_arg)):
                result = ETHERSCAN_API.getBalance(str(hex(first_arg)))   ## returns str
                SYM_STACK.append(int(result))
            else:
                new_var_name = GENERATOR.gen_balance_var(first_arg)
                result = 0
                if(new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'ORIGIN'):      # DONE
        result = CONTRACT_PROPERTIES['exec']['origin']
        result = int(result,16)
        SYM_STACK.append(result)
    elif (opcode == 'CALLER'):      # DONE
        result = CONTRACT_PROPERTIES["Is"]["address"]
        result = int(result, 16)
        SYM_STACK.append(result)
    elif (opcode == 'CALLVALUE'):   # DONE
        result = CONTRACT_PROPERTIES['exec']['value']
        result = int(result, 16)
        SYM_STACK.append(result)
    elif (opcode == 'CALLDATALOAD'):    # DONE
        global SYM_FIRST_CALLDATALOAD
        if(len(SYM_STACK) > 0 and SYM_FIRST_CALLDATALOAD):
            first_arg = SYM_STACK.pop()
            data = CONTRACT_PROPERTIES['exec']['calldata']
            result = data[(2 + 2 * first_arg):(66 + 2 * first_arg)]
            result = int(result, 16)
            SYM_STACK.append(result)
            SYM_FIRST_CALLDATALOAD = False
        elif (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            new_var_name = GENERATOR.gen_par_var()
            result = 0
            if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
            else:
                result = BitVec(new_var_name, 256)
                SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLDATASIZE'):    # DONE
        new_var_name = GENERATOR.gen_data_size()
        data = CONTRACT_PROPERTIES['exec']['calldata']
        result = int((len(data) - 2) / 2)
        SYM_STACK.append(result)
        #result = 0
        #if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
        #    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        #else:
        #    result = BitVec(new_var_name, 256)
        #    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        #SYM_STACK.append(result)
    elif (opcode == 'CALLDATACOPY'):    # DONE
        if (len(SYM_STACK) > 2):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            third_arg = SYM_STACK.pop()
            # NO WAY OF SIMULATION
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CODESIZE'):        # DONE
        f = open('bin.txt', 'r')
        bin_file = f.read()
        f.close()
        index = bin_file.index('part:')
        bin_file = bin_file[index + 7:][:-1]
        result = int(len(bin_file)/2)
        SYM_STACK.append(result)
    elif (opcode == 'CODECOPY'):        # DONE
        if (len(SYM_STACK) > 2):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            third_arg = SYM_STACK.pop()

            if(is_all_real(first_arg, second_arg, third_arg)):
                f = open('bin.txt', 'r')
                bin_file = f.read()
                f.close()
                index = bin_file.index('part:')
                bin_file = bin_file[index + 7:][:-1]

                for count in range(0, third_arg):
                    SYM_MEMORY[first_arg + count] = str(bin_file[2*(second_arg + count)]) + str(bin_file[2*(second_arg + count) + 1])
            else:
                new_var_name = GENERATOR.gen_mem_var(first_arg, third_arg)
                result = 0
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'GASPRICE'):        # DONE
        result = CONTRACT_PROPERTIES['exec']['gasPrice']
        result = int(result, 16)
        SYM_STACK.append(result)
    elif (opcode == 'EXTCODESIZE'):     # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            if(is_all_real(first_arg)):
                first_arg = hex(first_arg)
                result = int(len(ETHERSCAN_API.getCode(str(first_arg))) - 2)/2
                SYM_STACK.append(result)
            else:
                new_var_name = GENERATOR.gen_code_size_var(first_arg)
                result = 0
                if(new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'EXTCODECOPY'):     # DONE
        if (len(SYM_STACK) > 3):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            third_arg = SYM_STACK.pop()
            fourth_arg = SYM_STACK.pop()
            if(is_all_real(first_arg, second_arg, third_arg, fourth_arg)):
                code = ETHERSCAN_API.getCode(str(hex(first_arg)))[2:]
                for count in range(0, fourth_arg):
                    SYM_MEMORY[second_arg + count] = str(code[2*(third_arg + count)]) + str(code[2*(third_arg + count) + 1])
            else:
                new_var_name = GENERATOR.gen_mem_var(second_arg, fourth_arg)
                result = 0
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'BLOCKHASH'):       # NOT COMPLETE YET
        if (len(SYM_STACK) > 0):
            SYM_STACK.pop()
            #CONTRACT_PROPERTIES["IH_BLOCKHASH"] ... int(result, 16)
            new_var_name = "IH_BLOCKHASH"
            result = 0
            if(new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
            else:
                result = BitVec(new_var_name, 256)
                SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'COINBASE'):        # DONE
        #result = CONTRACT_PROPERTIES['env']['currentCoinbase']
        #result = int(result, 16)
        new_var_name = "IH_COINBASE"
        result = 0
        if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
            result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        else:
            result = BitVec(new_var_name, 256)
            SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'TIMESTAMP'):       # DONE
        #result = CONTRACT_PROPERTIES['env']['currentTimestamp']
        #result = int(result, 16)
        new_var_name = "IH_TIMESTAMP"
        result = 0
        if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
            result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        else:
            result = BitVec(new_var_name, 256)
            SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'NUMBER'):          # DONE
        #result = CONTRACT_PROPERTIES['env']['currentNumber']
        #result = int(result, 16)
        new_var_name = "IH_NUMBER"
        result = 0
        if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
            result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        else:
            result = BitVec(new_var_name, 256)
            SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'DIFFICULTY'):      # DONE
        #result = CONTRACT_PROPERTIES['env']['currentDifficulty']
        #result = int(result, 16)
        new_var_name = "IH_DIFFICULTY"
        result = 0
        if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
            result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        else:
            result = BitVec(new_var_name, 256)
            SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'GASLIMIT'):        # DONE
        #result = CONTRACT_PROPERTIES['env']['currentGasLimit']
        #result = int(result, 16)
        new_var_name = "IH_GASLIMIT"
        result = 0
        if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
            result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
        else:
            result = BitVec(new_var_name, 256)
            SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'POP'):             # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MLOAD'):           # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            new_var_name = GENERATOR.gen_mem_var(first_arg, 32)
            if(is_all_real(first_arg)):
                if(new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                    SYM_STACK.append(result)
                elif(len(SYM_MEMORY) < first_arg + 32):
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                    SYM_STACK.append(result)
                else:
                    k = ""
                    for i in range(0, 32):
                        k = k + SYM_MEMORY[first_arg + i]
                    result = int(k,16)
                    SYM_STACK.append(result)
            else:
                result = 0
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MSTORE'):          # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            new_var_name = GENERATOR.gen_mem_var(first_arg, 32)
            if(is_all_real(first_arg, second_arg)):
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    del SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                second_arg = str(hex(second_arg))[2:]
                len_arg = len(second_arg)
                if(len_arg < 64):
                    dif = 64 - len_arg
                    second_arg = "0"*dif + second_arg

                for i in range(0, 32):
                    SYM_MEMORY[first_arg + i] = second_arg[2*i:2*i + 2]
            else:
                if (is_all_real(second_arg)):
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = BitVecVal(second_arg, 256)
                else:
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = second_arg
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MSTORE8'):         # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            second_arg = second_arg & 255
            new_var_name = GENERATOR.gen_mem_var(first_arg, 8)
            if(is_all_real(first_arg, second_arg)):
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    del SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                SYM_MEMORY[first_arg] = str(hex(second_arg & 0xFF))[2:]
            else:
                if (is_all_real(second_arg)):
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = BitVecVal(second_arg, 256)
                else:
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = second_arg
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SLOAD'):           # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            if(is_all_real(first_arg)):
                result = SYM_STORAGE[first_arg]
                SYM_STACK.append(result)
            else:
                new_var_name = GENERATOR.gen_owner_store_var(first_arg)
                result = 0
                if (new_var_name in SYM_PATH_CONDITIONS_AND_VARS):
                    result = SYM_PATH_CONDITIONS_AND_VARS[new_var_name]
                else:
                    result = BitVec(new_var_name, 256)
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
                SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SSTORE'):          # DONE
        if (len(SYM_STACK) > 1):
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            new_var_name = GENERATOR.gen_owner_store_var(first_arg)
            if (is_all_real(first_arg, second_arg)):
                SYM_STORAGE[first_arg] = second_arg
            else:
                if (is_all_real(second_arg)):
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = BitVecVal(second_arg, 256)
                else:
                    SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = second_arg

        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'JUMP'):            # DONE
        if (len(SYM_STACK) > 0):
            first_arg = SYM_STACK.pop()
            #if(not(is_all_real(first_arg))):
            #    raise ValueError('JUMP ADDRESS SHOULD BE INTEGER')
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'JUMPI'):           # DONE          True --> '1' , False --> '0'
        global SYM_REQUEST_COND
        if (len(SYM_STACK) > 1):            ##TODO LATER
            first_arg = SYM_STACK.pop()
            second_arg = SYM_STACK.pop()
            if(is_all_real(second_arg)):
                do_not = 1
            else:
                SYM_REQUEST_COND = True
                SYM_PATH_CONDITIONS_AND_VARS["path_condition"].append(second_arg)

            #if(not(is_all_real(first_arg, second_arg))):
            #    will_do= 1
               ## TODO TREE CONSTRUCTION
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'PC'):              # DONE
        result = GLOBAL_STATE["pc"]
        SYM_STACK.append(result)
    elif (opcode == 'MSIZE'):           # DONE BUT NOT SURE --> NOT COMPLETE and len cannot be true one!!!
        result = len(MEMORY) + 32*len(SYM_PATH_CONDITIONS_AND_VARS)
        SYM_STACK.append(result)
    elif (opcode == 'GAS'):             # DONE
        new_var_name = GENERATOR.gen_gas_var()
        result = BitVec(new_var_name, 256)
        SYM_PATH_CONDITIONS_AND_VARS[new_var_name] = result
        SYM_STACK.append(result)
    elif (opcode == 'JUMPDEST'):        # DONE
        dont_do_anything = 1
    elif (opcode.startswith('PUSH', 0)):    # DONE
        position = int(opcode[4:], 10)
        old_pc = GLOBAL_STATE["pc"]
        index = FILE_PC_OPCODES.index(old_pc)
        result = FILE_OPCODES[index].par
        SYM_STACK.append(result)
    elif (opcode.startswith("DUP", 0)):     # DONE
        position = int(opcode[3:], 10)
        if(len(SYM_STACK) > position-1):
            result = SYM_STACK[len(SYM_STACK)-position]
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode.startswith("SWAP", 0)):    # DONE
        position = int(opcode[4:], 10)
        if (len(SYM_STACK) > position):
            temp = SYM_STACK[len(SYM_STACK) - 1 - position]
            SYM_STACK[len(SYM_STACK) - 1 - position] = SYM_STACK[len(SYM_STACK) - 1]
            SYM_STACK[len(SYM_STACK) - 1] = temp
        else:
            raise ValueError('STACK underflow')
    elif (opcode.startswith("LOG", 0)):     # DONE
        position = int(opcode[3:], 10)
        if(len(SYM_STACK) > position + 1):
            for a in range(0, position+2):
                SYM_STACK.pop()
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CREATE'):      # DONE
        if (len(SYM_STACK) > 2):
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()

            result = BitVec(GENERATOR.gen_arbitrary_var(), 256)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALL'):        # DONE    TODO Money depends on time ?
        if (len(SYM_STACK) > 6):
            outgas = SYM_STACK.pop()
            recipient = SYM_STACK.pop()
            transfer_amount = SYM_STACK.pop()
            start_data_input = SYM_STACK.pop()
            size_data_input = SYM_STACK.pop()
            start_data_output = SYM_STACK.pop()
            size_data_ouput = SYM_STACK.pop()

            if(transfer_amount == 0):
                SYM_STACK.append(1)
                return
            my_balance = "my_balance"
            if(my_balance in SYM_PATH_CONDITIONS_AND_VARS):
                SYM_PATH_CONDITIONS_AND_VARS[my_balance] = SYM_PATH_CONDITIONS_AND_VARS[my_balance] - transfer_amount
            else:
                new_my_balance = BitVec(my_balance, 256)
                SYM_PATH_CONDITIONS_AND_VARS[my_balance] = new_my_balance - transfer_amount
            SYM_PATH_CONDITIONS_AND_VARS["path_condition"].append(SYM_PATH_CONDITIONS_AND_VARS[my_balance] >= 0)

            other_balance = str(recipient) + "_balance"
            if (other_balance in SYM_PATH_CONDITIONS_AND_VARS):
                SYM_PATH_CONDITIONS_AND_VARS[other_balance] = SYM_PATH_CONDITIONS_AND_VARS[other_balance] + transfer_amount
            else:
                new_other_balance = BitVec(other_balance, 256)
                SYM_PATH_CONDITIONS_AND_VARS[other_balance] = new_other_balance + transfer_amount
            SYM_STACK.append(1)

                #if (is_enough_fund):
                #   SYM_CONTRACT_PROPERTIES["Ia"]["balance"] = balance - transfer_amount
                #   SYM_CONTRACT_PROPERTIES["Is"]["balance"] = SYM_CONTRACT_PROPERTIES["Is"]["balance"] + transfer_amount
                #   SYM_STACK.append(1)
                #else:
                #    SYM_STACK.append(0)    We assume all operations have enough fund
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLCODE'):    # DONE  TODO money depends on time ?
        if (len(SYM_STACK) > 6):
            outgas = SYM_STACK.pop()
            recipient = SYM_STACK.pop()
            transfer_amount = SYM_STACK.pop()
            start_data_input = SYM_STACK.pop()
            size_data_input = SYM_STACK.pop()
            start_data_output = SYM_STACK.pop()
            size_data_ouput = SYM_STACK.pop()

            if (transfer_amount == 0):
                SYM_STACK.append(1)
                return
            my_balance = "my_balance"
            if (my_balance in SYM_PATH_CONDITIONS_AND_VARS):
                SYM_PATH_CONDITIONS_AND_VARS[my_balance] = SYM_PATH_CONDITIONS_AND_VARS[my_balance] - transfer_amount
            else:
                new_my_balance = BitVec(my_balance, 256)
                SYM_PATH_CONDITIONS_AND_VARS[my_balance] = new_my_balance - transfer_amount
            SYM_PATH_CONDITIONS_AND_VARS["path_condition"].append(SYM_PATH_CONDITIONS_AND_VARS[my_balance] >= 0)

            other_balance = str(recipient) + "_balance"
            if (other_balance in SYM_PATH_CONDITIONS_AND_VARS):
                SYM_PATH_CONDITIONS_AND_VARS[other_balance] = SYM_PATH_CONDITIONS_AND_VARS[
                                                                  other_balance] + transfer_amount
            else:
                new_other_balance = BitVec(other_balance, 256)
                SYM_PATH_CONDITIONS_AND_VARS[other_balance] = new_other_balance + transfer_amount
            SYM_STACK.append(1)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'RETURN'):  # DONE
        if (len(SYM_STACK) > 1):
            SYM_STACK.pop()
            SYM_STACK.pop()         # TODO What happens to returned value, where it kept
            return 444
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'DELEGATECALL'):    # DONE
        if (len(SYM_STACK) > 5):
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            result = BitVec(GENERATOR.gen_arbitrary_var(), 256)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLBLACKBOX'):    # DONE
        if (len(SYM_STACK) > 4):
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            result = BitVec(GENERATOR.gen_arbitrary_var(), 256)
            SYM_STACK.append(result) #address
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'STATICCALL'):  # DONE
        if (len(SYM_STACK) > 5):
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            SYM_STACK.pop()
            result = BitVec(GENERATOR.gen_arbitrary_var(), 256)
            SYM_STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'REVERT'):  # DONE
        if (len(SYM_STACK) > 1):
            SYM_STACK.pop()
            SYM_STACK.pop()
            return 444
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'INVALID'): # DONE
        return 111
    elif (opcode == 'SUICIDE'): # DONE
        if (len(SYM_STACK) > 0):
            SYM_STACK.pop()
            #transfer_amount = CONTRACT_PROPERTIES["Ia"]["balance"] = int(balance - transfer_amount, 16)
            CONTRACT_PROPERTIES["Ia"]["balance"] = "0x0"
            return 444
        else:
            raise ValueError('STACK underflow')

"""
444 --> STOP
222 --> STACK UNDERFLOW
111 --> INVALID
1   --> OK
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
            raise ValueError('STACK underflow')
    elif (opcode == 'MUL'):     # DONE
        if(len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = (first_arg * second_arg) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SUB'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = to_unsigned((first_arg - second_arg)) & (UNSIGNED_BOUND_NUMBER)
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
                result = to_unsigned(sign * (abs(first_arg) // abs(second_arg)))
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
                result = to_unsigned(sign * (abs(first_arg) % abs(second_arg)))
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
    elif (opcode == 'EXP'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = (first_arg ** second_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
    elif (opcode == 'ISZERO'):  # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = 0
            if first_arg == 0:
                result = 1
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'AND'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg & second_arg
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'OR'):      # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg | second_arg
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'XOR'):     # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            result = first_arg ^ second_arg
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'NOT'):     # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            result = (~first_arg) & UNSIGNED_BOUND_NUMBER
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
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
            raise ValueError('STACK underflow')
    elif (opcode == 'ADDRESS'):     # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['Ia']['address']
        result = int(result,16)
        STACK.append(str(result))
    elif (opcode == 'BALANCE'):     # DONE
        if len(STACK) > 0:
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = hex(int(STACK.pop()))
            result = ETHERSCAN_API.getBalance(str(first_arg))   ## returns str
            STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'ORIGIN'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['origin']
        result = int(result,16)
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
    elif (opcode == 'CALLDATALOAD'):    # DONE TODO first arg mul by 2 or not ???
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            data = CONTRACT_PROPERTIES['exec']['calldata']
            result = data[(2+2*first_arg):(66+2*first_arg)]
            result = int(result,16)
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLDATASIZE'):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        data = CONTRACT_PROPERTIES['exec']['calldata']
        result = int((len(data)-2)/2)
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
            raise ValueError('STACK underflow')
    elif (opcode == 'CODESIZE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1

        f = open('bin.txt', 'r')
        bin_file = f.read()
        f.close()
        index = bin_file.index('part:')
        bin_file = bin_file[index + 7:][:-1]

        result = int(len(bin_file)/2)
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
            raise ValueError('STACK underflow')
    elif (opcode == 'GASPRICE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['exec']['gasPrice']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'EXTCODESIZE'):     # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = hex(int(STACK.pop()))
            result = int(len(ETHERSCAN_API.getCode(str(first_arg))) - 2)/2
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'EXTCODECOPY'):     # DONE
        if (len(STACK) > 3):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())
            third_arg = int(STACK.pop())
            fourth_arg = int(STACK.pop())

            code = ETHERSCAN_API.getCode(str(hex(first_arg)))[2:]

            for count in range(0, fourth_arg):
                MEMORY[second_arg + count] = str(code[2*(third_arg + count)]) + str(code[2*(third_arg + count) + 1])
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'BLOCKHASH'):       # NOT COMPLETE YET
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            result = CONTRACT_PROPERTIES["IH_BLOCKHASH"]
            result = int(result, 16)
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'COINBASE'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['env']['currentCoinbase']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'TIMESTAMP'):       # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['env']['currentTimestamp']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'NUMBER'):          # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['env']['currentNumber']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'DIFFICULTY'):      # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['env']['currentDifficulty']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'GASLIMIT'):        # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = CONTRACT_PROPERTIES['env']['currentGasLimit']
        result = int(result, 16)
        STACK.append(str(result))
    elif (opcode == 'POP'):             # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MLOAD'):           # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())

            k = ""
            for i in range(0, 32):
                k = k + MEMORY[first_arg + i]
            result = int(k,16)
            STACK.append(str(result))
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MSTORE'):          # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())

            second_arg = str(hex(second_arg))[2:]

            len_arg = len(second_arg)
            if(len_arg < 64):
                dif = 64 - len_arg
                second_arg = "0"*dif + second_arg

            for i in range(0, 32):
                MEMORY[first_arg + i] = second_arg[2*i:2*i + 2]
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'MSTORE8'):         # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = int(STACK.pop())
            second_arg = int(STACK.pop())

            MEMORY[first_arg] = str(hex(second_arg & 0xFF))[2:]
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SLOAD'):           # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            result = STORAGE[first_arg]
            STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'SSTORE'):          # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            first_arg = STACK.pop()
            second_arg = STACK.pop()
            STORAGE[first_arg] = second_arg
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'JUMP'):            # DONE
        if (len(STACK) > 0):
            first_arg = int(STACK.pop())
            GLOBAL_STATE["pc"] = first_arg
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'JUMPI'):           # DONE          True --> '1' , False --> '0'
        global SYM_REQUEST_COND
        if (len(STACK) > 1):
            first_arg = int(STACK.pop())
            second_arg = STACK.pop()
            if second_arg == "1":    # "1" will represent true and "0" will be false
                GLOBAL_STATE["pc"] = first_arg
                if(SYM_REQUEST_COND):
                    SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"].append(True)
                    SYM_REQUEST_COND = False
            else:
                GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
                if(SYM_REQUEST_COND):
                    SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"].append(False)
                    SYM_REQUEST_COND = False
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'PC'):              # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = GLOBAL_STATE["pc"] - 1
        STACK.append(str(result))
    elif (opcode == 'MSIZE'):           # DONE BUT NOT SURE --> NOT COMPLETE and len cannot be true one!!!
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = len(MEMORY)
        STACK.append(str(result))
    elif (opcode == 'GAS'):             # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        result = GLOBAL_STATE["currentGas"]
        STACK.append(str(result))
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
            result = STACK[len(STACK)-position]
            STACK.append(result)
        else:
            raise ValueError('STACK underflow')
    elif (opcode.startswith("SWAP", 0)):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        position = int(opcode[4:], 10)
        if (len(STACK) > position):
            temp = STACK[len(STACK) - 1 - position]
            STACK[len(STACK) - 1 - position] = STACK[len(STACK) - 1]
            STACK[len(STACK) - 1] = temp
        else:
            raise ValueError('STACK underflow')
    elif (opcode.startswith("LOG", 0)):     # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        position = int(opcode[3:], 10)
        if(len(STACK) > position + 1):
            for a in range(0, position+2):
                STACK.pop()
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CREATE'):      # DONE
        if (len(STACK) > 2):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()

            STACK.append("888888888888888")
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALL'):        # DONE
        if (len(STACK) > 6):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            outgas = STACK.pop()
            recipient = STACK.pop()
            transfer_amount = int(STACK.pop())
            start_data_input = STACK.pop()
            size_data_input = STACK.pop()
            start_data_output = STACK.pop()
            size_data_ouput = STACK.pop()

            balance = int(CONTRACT_PROPERTIES["Ia"]["balance"],16)
            is_enough_fund = (transfer_amount <= balance)

            if(is_enough_fund):
                CONTRACT_PROPERTIES["Ia"]["balance"] = str(hex(balance - transfer_amount))
                CONTRACT_PROPERTIES["Is"]["balance"] = str(hex(int(CONTRACT_PROPERTIES["Is"]["balance"],16) + transfer_amount))
                STACK.append("1")
            else:
                STACK.append("0")

        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLCODE'):    # DONE
        if (len(STACK) > 6):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            outgas = STACK.pop()
            recipient = STACK.pop()
            transfer_amount = int(STACK.pop())
            start_data_input = STACK.pop()
            size_data_input = STACK.pop()
            start_data_output = STACK.pop()
            size_data_ouput = STACK.pop()

            balance = int(CONTRACT_PROPERTIES["Ia"]["balance"], 16)
            is_enough_fund = (transfer_amount <= balance)

            if (is_enough_fund):
                CONTRACT_PROPERTIES["Ia"]["balance"] = str(hex(balance - transfer_amount))
                CONTRACT_PROPERTIES["Is"]["balance"] = str(hex(int(CONTRACT_PROPERTIES["Is"]["balance"], 16) + transfer_amount))
                STACK.append("1")
            else:
                STACK.append("0")
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'RETURN'):  # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()         # TODO What happens to returned value, where it kept
            return 444
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'DELEGATECALL'):    # DONE
        if (len(STACK) > 5):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.append("1")
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'CALLBLACKBOX'):    # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
        if (len(STACK) > 4):
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.append("999999999999") #address
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'STATICCALL'):  # DONE
        if (len(STACK) > 5):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()
            STACK.pop()

            STACK.append("1")
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'REVERT'):  # DONE
        if (len(STACK) > 1):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            STACK.pop()
            return 444
        else:
            raise ValueError('STACK underflow')
    elif (opcode == 'INVALID'): # DONE
        return 111
    elif (opcode == 'SUICIDE'): # DONE
        if (len(STACK) > 0):
            GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1
            STACK.pop()
            #transfer_amount = CONTRACT_PROPERTIES["Ia"]["balance"] = int(balance - transfer_amount, 16)
            CONTRACT_PROPERTIES["Ia"]["balance"] = "0x0"
            return 444
        else:
            raise ValueError('STACK underflow')
    else:   # DONE
        GLOBAL_STATE["pc"] = GLOBAL_STATE["pc"] + 1

def to_unsigned(num):
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
        ret = ret + MEMORY[offset + a]
    return int(ret, 16)

def read_from_mem_sym(offset, length):
    ret = ""
    for a in range(0,length):
        ret = ret + MEMORY[offset + a]
    return int(ret, 16)

# Checks that given parameter is z3 expression or not
def is_symbolic(exp):
    return z3.is_expr(exp)

def is_all_real(*args):
    for element in args:
        if (is_symbolic(element)):
            return False
    return True

def to_symbolic(number):
    if (is_symbolic(number)):
        return number
    return BitVecVal(number, 256)

def isReal(value):
    return isinstance(value, six.integer_types)

def check_sat(pop_if_exception=True):
    try:
        ret = Symbolic_Solver.check()
        if ret == unknown:
            raise Z3Exception(Symbolic_Solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            Symbolic_Solver.pop()
        raise e
    return ret

def init_etherscan():
    global ETHERSCAN_API
    ETHERSCAN_API = EthereumData()

def reset_inputs():
    global GENERATOR
    global GLOBAL_STATE
    global STACK
    global MEMORY
    global STORAGE
    global SYM_REQUEST_COND
    global SYM_FIRST_CALLDATALOAD
    global SYM_STACK
    global SYM_MEMORY
    global SYM_PATH_CONDITIONS_AND_VARS
    global SYM_STORAGE
    global EXECUTION_PATH_TREE
    global CONTRACT_PROPERTIES
    GENERATOR = generator.Generator()
    GLOBAL_STATE = {"currentGas": 1000, "pc": 0}
    STACK = []
    MEMORY = helper.GrowingList()
    STORAGE = {}
    SYM_REQUEST_COND = False
    SYM_FIRST_CALLDATALOAD = True
    SYM_STACK = []
    SYM_MEMORY = helper.GrowingList()
    SYM_PATH_CONDITIONS_AND_VARS = {"path_condition": [], "path_condition_status": []}
    SYM_STORAGE = {}
    CONTRACT_PROPERTIES = {
        "env": {
            "currentCoinbase": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",  # COINBASE
            "currentDifficulty": "0x0100",  # DIFFICULTY
            "currentGasLimit": "0x0f4240",  # GASLIMIT
            "currentNumber": "0x00",  # NUMBER
            "currentTimestamp": "0x00"  # TIMESTAMP
        },
        "exec": {
            "data": "0xff",
            "calldata": "0xfbac12f386434657432ababbaccccccdddff1231256787ac12f386434657432ababbaccccccdddfac12f386434657432ababbaccccccdddf",
            # CALLDATALOAD-CALLDATASIZE-CALLDATACOPY, input data
            "gas": "0x0186a0",
            "gasPrice": "0x5af3107a4000",  # GASPRICE
            "origin": "0xcd1722f3947def4cf144679da39c4c32bdc35681",  # origin address, sender of original transaction.
            "value": "0x0"  # CALLVALUE, deposited value by the instruction/transaction
        },
        "gas": "0x013874",
        "Is": {
            "address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",  # CALLER, directly responsible for this execution.
            "balance": "0xbb"  # CALL, their balance
        },
        "Ia": {
            "address": "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",  # ORIGIN, currently executing account.
            "balance": "0xcc",  # CALL, my balance
            "storage": {
                "0x00": "0x2222"
            }
        },
        "IH_BLOCKHASH": "0x0012"  # BLOCKHASH
    }

    """ if (is_all_real(transfer_amount)):
                    if (transfer_amount == 0):
                        SYM_STACK.append(1)
                        return

                    balance = int(SYM_CONTRACT_PROPERTIES["Ia"]["balance"], 16)
                    is_enough_fund = (transfer_amount <= balance)

                    if (is_enough_fund):
                        SYM_CONTRACT_PROPERTIES["Ia"]["balance"] = str(hex(balance - transfer_amount))
                        SYM_CONTRACT_PROPERTIES["Is"]["balance"] = str(hex(int(SYM_CONTRACT_PROPERTIES["Is"]["balance"], 16) + transfer_amount))
                        SYM_STACK.append(1)
                    else:
                        SYM_STACK.append(0)

                else:
                    SYM_STACK.append(1)  ## Guessing possibly okay"""