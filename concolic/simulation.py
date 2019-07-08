"""
SIMULATION ATOMS
"""
GLOBAL_STATE= {}

STACK = []

MEMORY = []
next_mem_loc = 0

STORAGE = {}

"""
USEFUL STUFFS
"""
UNSIGNED_BOUND_NUMBER = 2**256 - 1

NEGATIVE_BOUND_NUMBER = 2**256

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
    elif (opcode == 'BYTE'):
        print("asd")
    elif (opcode == 'KECCAK256'):
        print("asd")
    elif (opcode == 'ADDRESS'):
        print("asd")
    elif (opcode == 'BALANCE'):
        print("asd")
    elif (opcode == 'ORIGIN'):
        print("asd")
    elif (opcode == 'CALLER'):
        print("asd")
    elif (opcode == 'CALLVALUE'):
        print("asd")
    elif (opcode == 'CALLDATALOAD'):
        print("asd")
    elif (opcode == 'CALLDATASIZE'):
        print("asd")
    elif (opcode == 'CALLDATACOPY'):
        print("asd")
    elif (opcode == 'CODESIZE'):
        print("asd")
    elif (opcode == 'CODECOPY'):
        print("asd")
    elif (opcode == 'GASPRICE'):
        print("asd")
    elif (opcode == 'EXTCODESIZE'):
        print("asd")
    elif (opcode == 'EXTCODECOPY'):
        print("asd")
    elif (opcode == 'BLOCKHASH'):
        print("asd")
    elif (opcode == 'COINBASE'):
        print("asd")
    elif (opcode == 'TIMESTAMP'):
        print("asd")
    elif (opcode == 'NUMBER'):
        print("asd")
    elif (opcode == 'DIFFICULTY'):
        print("asd")
    elif (opcode == 'GASLIMIT'):
        print("asd")
    elif (opcode == 'POP'):
        print("asd")
    elif (opcode == 'MLOAD'):
        print("asd")
    elif (opcode == 'MSTORE'):
        print("asd")
    elif (opcode == 'MSTORE8'):
        print("asd")
    elif (opcode == 'SLOAD'):
        print("asd")
    elif (opcode == 'SSTORE'):
        print("asd")
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