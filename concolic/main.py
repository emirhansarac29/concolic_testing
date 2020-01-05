import shlex
import subprocess
import math
import os
import sys
import re
import six
from z3 import *
import generator

import opcodes
import basicblock
import simulation

# BLOCK NUMBER DEPENDENCY SOLVED
# TIMESTAMP DEPENDENCY SOLVED
# TOD DEPENDENCY SOLVED
# REENTRANCY SOLVED
# MISHANDLED EXCEPTION SOLVED
NEXT_TRACE = []
MAXIMUM_FUNCTION_RUN = 100

class OPCODE:
    def __init__(self, name, par):
        self.name = name
        self.par = par


class FUNCTION:
    def __init__(self, begin, signature, class_begin_pc):
        self.begin = begin
        self.signature = signature
        self.class_begin_pc = class_begin_pc


def get_opcodes(bin_file):
    arr_opc = []
    arr_pc_opc = []
    lens = len(bin_file)
    bin_file = bin_file[0:lens - 1]
    lens = lens - 1

    index = 0
    while (index <= lens - 2):
        opc_number = bin_file[index:index + 2]
        if (opcodes.opcodes.get(opc_number) == None):
            arr_opc.append(OPCODE('ERROR', ''))
            arr_pc_opc.append(index / 2)
            index = index + 2
        else:
            op_name = opcodes.opcodes.get(opc_number)
            arr_pc_opc.append(index / 2)
            index = index + 2
            op_par = int(opcodes.op_param.get(op_name))
            if (op_par != 0):
                opc_param = bin_file[index:index + op_par]
                arr_opc.append(OPCODE(op_name, int(opc_param, 16)))  # INTEGER
                # arr_opc.append(OPCODE(op_name, opc_param))				# HEX
                index = index + op_par
            else:
                arr_opc.append(OPCODE(op_name, ''))

    return arr_opc, arr_pc_opc


def find_basic_blocks(FILE_OPCODES, FILE_PC_OPCODES):
    separators = ['JUMPI', 'STOP', 'RETURN', 'SUICIDE', 'JUMP', 'JUMPDEST']
    basic_blocks = []
    init_pc = 0
    for opc_number in range(len(FILE_OPCODES)):
        opc = FILE_OPCODES[opc_number]
        if (opc.name in separators and init_pc != FILE_PC_OPCODES[opc_number]):
            dest = []
            if (opc.name == 'JUMPDEST'):
                dest.append(FILE_PC_OPCODES[opc_number] + 1)
            elif (opc.name == 'JUMP' and re.search('PUSH*', FILE_OPCODES[opc_number - 1].name)):
                dest.append(FILE_OPCODES[opc_number - 1].par)
            elif (opc.name == 'JUMPI' and re.search('PUSH*', FILE_OPCODES[opc_number - 1].name)):
                dest.append(FILE_PC_OPCODES[opc_number] + 1)
                dest.append(FILE_OPCODES[opc_number - 1].par)
            pc = FILE_PC_OPCODES[opc_number]
            basic_blocks.append(basicblock.BasicBlock(init_pc, pc, opc.name, dest))
            init_pc = FILE_PC_OPCODES[opc_number + 1]
    return basic_blocks

def find_functions(FILE_OPCODES, FILE_PC_OPCODES):
    functions = []
    classes = []
    for num in range(0, len(FILE_OPCODES)):
        if(num + 2 < len(FILE_OPCODES)):
            if(FILE_OPCODES[num].name == "PUSH1" and FILE_OPCODES[num].par == 128 and FILE_OPCODES[num+1].name == "PUSH1" and FILE_OPCODES[num+1].par == 64 and FILE_OPCODES[num+2].name == "MSTORE" and FILE_OPCODES[num+2].par == ""):
                classes.append(num)
    for class_position in classes:
        for num in range(class_position, len(FILE_OPCODES)):
            if (FILE_OPCODES[num].name == "REVERT"):
                break
            if (FILE_OPCODES[num].name == "DUP1" and FILE_OPCODES[num + 1].name == "PUSH4" and FILE_OPCODES[
                num + 2].name == "EQ" and re.search('PUSH*', FILE_OPCODES[num + 3].name) and FILE_OPCODES[
                num + 4].name == "JUMPI"):
                functions.append(FUNCTION(FILE_OPCODES[num + 3].par + FILE_PC_OPCODES[class_position], FILE_OPCODES[num + 1].par, FILE_PC_OPCODES[class_position]))
    return functions


def find_parameters(FUNCTIONS, FILE_OPCODES, FILE_PC_OPCODES, FILE_PC_TO_INDEX):
    parameters = {}
    for func in FUNCTIONS:
        pars = []

        pos = 0
        for i in range(0, len(FILE_PC_OPCODES)):
            if (FILE_PC_OPCODES[i] == func.begin):
                pos = i
                break

        # for i in range(pos, len(FILE_OPCODES)):
        #	if(FILE_OPCODES[i].name == "CALLDATASIZE"):
        #		pos = i
        #		break
        count = 0
        rem = 3
        for i in range(pos, len(FILE_OPCODES)):
            if (FILE_OPCODES[i].name == "JUMPDEST"):
                rem = rem - 1
                if (rem == 0):
                    break
            elif (FILE_OPCODES[i].name == "CALLDATALOAD"):
                if (count > 0):
                    count = count - 1
                elif (FILE_OPCODES[i + 1].name == "ISZERO"):
                    pars.append("bool")
                elif (FILE_OPCODES[i + 1].name == "SWAP1"):
                    if (FILE_OPCODES[i + 5].name == "DUP3"):
                        pars.append("string")
                        count = 1
                    else:
                        pars.append("int256")
                elif (re.search('PUSH*', FILE_OPCODES[i + 1].name)):
                    if (FILE_OPCODES[i + 2].name == "NOT"):
                        pars.append("bytes" + str(32 - opcodes.byte_values.get(str(FILE_OPCODES[i + 1].par))))
                    elif (FILE_OPCODES[i + 2].name == "AND"):
                        pars.append("uint" + str(8 * opcodes.byte_values.get(str(FILE_OPCODES[i + 1].par))))
                    elif (FILE_OPCODES[i + 2].name == "SIGNEXTEND"):
                        pars.append("int" + str(8 * (FILE_OPCODES[i + 1].par + 1)))

        parameters[func.signature] = pars

    return parameters

def reset_and_set_initials(trace, number_of_pars, hex_f_id):
    t_trace = trace
    root = simulation.EXECUTION_PATH_TREE
    temp = root
    solver_next = Solver()
    for a in t_trace:
        if(a == 0):
            solver_next.add(root["condition"] == False)
            root = root[0]
        else:
            solver_next.add(root["condition"] == True)
            root = root[1]
    for mis_pos in range(len(simulation.MISHANDLED_EXCEPTION_SYM_VAR_EQS)):
        solver_next.add(simulation.MISHANDLED_EXCEPTION_SYM_VARS[mis_pos] == simulation.MISHANDLED_EXCEPTION_SYM_VAR_EQS[mis_pos])
    if(solver_next.check() != z3.sat):
        temp_2 = temp
        for a in t_trace:
            temp_2 = temp
            temp = temp[a]
        temp_2[t_trace[len(t_trace)-1]] = "unsat"
        print("UNSATISFIED TRACE DETECTED")
        return "unsat"
    else:
        model = solver_next.model()
        print(model)
        exec_calldata = hex_f_id
        new_datas = {}
        for a in range(number_of_pars):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["parameter_" + str(a + 1)]]
            if(par == None):
                exec_calldata = exec_calldata + (64 * "1")
            else:
                val_hex = hex(int(str(par)))[2:]
                h_l = 64 - len(val_hex)
                if(h_l > 0):
                    val_hex = ("0" * h_l) + val_hex
                exec_calldata = exec_calldata + val_hex
        simulation.CONTRACT_PROPERTIES['exec']['calldata'] = exec_calldata
        if ("IH_BLOCKHASH" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_BLOCKHASH"]]
            if(par != None):
                simulation.CONTRACT_PROPERTIES["IH_BLOCKHASH"] = hex(int(str(par)))
        if ("IH_COINBASE" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_COINBASE"]]
            if (par != None):
                simulation.CONTRACT_PROPERTIES['env']['currentCoinbase'] = hex(int(str(par)))
        if ("IH_TIMESTAMP" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_TIMESTAMP"]]
            if (par != None):
                simulation.CONTRACT_PROPERTIES['env']['currentTimestamp'] = hex(int(str(par)))
        if ("IH_NUMBER" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_NUMBER"]]
            if (par != None):
                simulation.CONTRACT_PROPERTIES['env']['currentNumber'] = hex(int(str(par)))
        if ("IH_DIFFICULTY" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_DIFFICULTY"]]
            if (par != None):
                simulation.CONTRACT_PROPERTIES['env']['currentDifficulty'] = hex(int(str(par)))
        if ("IH_GASLIMIT" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            par = model[simulation.SYM_PATH_CONDITIONS_AND_VARS["IH_GASLIMIT"]]
            if (par != None):
                simulation.CONTRACT_PROPERTIES['env']['currentGasLimit'] = hex(int(str(par)))
        if ("my_balance" in simulation.SYM_PATH_CONDITIONS_AND_VARS.keys()):
            my_balance = BitVec("my_balance", 256)
            par = model[my_balance]
            if (par != None):
                simulation.CONTRACT_PROPERTIES["Ia"]["balance"] = hex(int(str(par)))
        storage_points = []
        for item in simulation.STORAGE.keys():
            storage_points.append(item)
        simulation.reset_inputs()
        for item in storage_points:
            storage = BitVec(simulation.GENERATOR.gen_owner_store_var(item), 256)
            n_storage = model[storage]
            if(n_storage != None):
                simulation.STORAGE[item] = str(n_storage)
        return "sat"


def re_find_new_path_trace(leaf, current_trace):
    global NEXT_TRACE
    if(leaf["condition"] == None):
        return
    if(leaf[0] == None):
        NEXT_TRACE = current_trace + [0]
    if (leaf[1] == None):
        NEXT_TRACE = current_trace + [1]
    if(leaf[0] != None and leaf[0] != "unsat"):
        re_find_new_path_trace(leaf[0], current_trace + [0])
    if(leaf[1] != None and leaf[1] != "unsat"):
        re_find_new_path_trace(leaf[1], current_trace + [1])


def find_new_path_trace():
    root = simulation.EXECUTION_PATH_TREE
    current_trace = []
    if(root["condition"] == None):
        return []
    re_find_new_path_trace(root, current_trace)

"""
solc --bin-runtime asd.sol > bin.txt
solc --optimize --opcodes asd.sol 
"""

def main():
    global NEXT_TRACE
    if (len(sys.argv) != 2):
        exit()
    solidity_file = sys.argv[1]
    os.system("solc --bin-runtime " + solidity_file + " > bin.txt")
    f = open('bin.txt', 'r')
    bin_file = f.read()
    f.close()

    index = bin_file.index('part:')
    bin_file = bin_file[index + 7:]

    FILE_OPCODES, FILE_PC_OPCODES = get_opcodes(bin_file)
    for a in range(len(FILE_PC_OPCODES)):
        FILE_PC_OPCODES[a] = int(FILE_PC_OPCODES[a])

    FILE_PC_TO_INDEX = {}
    for a in range(len(FILE_OPCODES)):
        FILE_PC_TO_INDEX[FILE_PC_OPCODES[a]] = a
        print("[" + str(FILE_PC_OPCODES[a]) + "]" + " " + FILE_OPCODES[a].name + "  " + str(FILE_OPCODES[a].par))

    #print(len(FILE_PC_OPCODES))
    #print(len(FILE_OPCODES))

    basic_blocks = find_basic_blocks(FILE_OPCODES, FILE_PC_OPCODES)
    #for i in basic_blocks:
    #    print(str(i.start) + " <-> " + str(i.end) + " <-> " + i.termination + " <-> " + str(i.targets))

    FUNCTIONS = find_functions(FILE_OPCODES, FILE_PC_OPCODES)
    for a in FUNCTIONS:
        print(str(a.begin) + " <-> " + str(a.signature) + " (" + str(hex(int(a.signature))) + ")" + " class starts at pc  " + str(a.class_begin_pc))

    FUNCTION_PARAMETERS = find_parameters(FUNCTIONS, FILE_OPCODES, FILE_PC_OPCODES, FILE_PC_TO_INDEX)
    print(FUNCTION_PARAMETERS)
    #print("IT SHOULD BE NOTED THAT ---->  uint160 == address and uint256 == int256")

    CODE_COVERAGE = []
    # Only static parameters will be used, not string and bytes
    for function in FUNCTIONS:
        f_id = function.signature
        f_begin_pc = function.begin
        f_begin_index = FILE_PC_TO_INDEX[f_begin_pc]

        number_of_pars = len(FUNCTION_PARAMETERS[f_id])
        hex_f_id = hex(f_id)[2:]
        h_l = 8 - len(hex_f_id)
        if (h_l > 0):
            hex_f_id = "0x" + str(("0" * h_l)) + hex_f_id
        else:
            hex_f_id = "0x" + hex_f_id
        simulation.reset_inputs()
        simulation.EXECUTION_PATH_TREE = {"condition" : None, 0 : None, 1 : None}
        simulation.CONTRACT_PROPERTIES['exec']['calldata'] = hex_f_id + ((64*number_of_pars) * "1")
        print("FUNCTION " + str(hex_f_id) + " will be tested")

        remaining_run = MAXIMUM_FUNCTION_RUN
        while(True):
            remaining_run = remaining_run - 1
            simulation.GLOBAL_STATE["pc"] = function.class_begin_pc
            print("EXECUTION PARS --> " + str(simulation.CONTRACT_PROPERTIES['exec']['calldata']))
            while(True):
                if(simulation.GLOBAL_STATE["pc"] not in CODE_COVERAGE):
                    CODE_COVERAGE.append(simulation.GLOBAL_STATE["pc"])
                op_name = FILE_OPCODES[FILE_PC_TO_INDEX[simulation.GLOBAL_STATE["pc"]]].name
                if (op_name == "RETURN" or op_name == "REVERT" or op_name == "STOP"):
                    break
                simulation.symbolic_execute_opcode(op_name, FILE_OPCODES,FILE_PC_OPCODES)
                simulation.execute_opcode(op_name, FILE_OPCODES, FILE_PC_OPCODES)
            #print(simulation.MEMORY)
            #print(simulation.STORAGE)

            ###     BEGIN MISHANDLED EXCEPTION BUG CHECK   ###
            for element_m_ex_ret in simulation.MISHANDLED_EXCEPTION_SYM_VARS:
                if(str(element_m_ex_ret) not in simulation.MISHANDLED_CHECKED_RETURNS):
                    simulation.CONCOLIC_RESULTS.append({"function": str(hex_f_id), "warning": "MISHANDLED EXCEPTION BUG"})
                    break
            ###     END MISHANDLED EXCEPTION BUG CHECK     ###

            #print("PATH --> " + str(simulation.EXECUTION_PATH_TREE))
            #print(simulation.SYM_PATH_CONDITIONS_AND_VARS)
            current_leaf = simulation.EXECUTION_PATH_TREE
            for cond in range(len(simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition"])):
                if(current_leaf["condition"] == None):
                    path_way = 0
                    if(simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"][0]):
                        path_way = 1
                    current_leaf["condition"] = simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition"][0]
                    current_leaf[path_way] = {"condition" : None, 0 : None, 1 : None}
                    current_leaf = current_leaf[path_way]
                    simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition"].pop(0)
                    simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"].pop(0)
                else:
                    path_way = 0
                    if (simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"][0]):
                        path_way = 1
                    if(current_leaf[path_way] == None):
                        current_leaf[path_way] = {"condition" : None, 0 : None, 1 : None}
                    current_leaf = current_leaf[path_way]
                    simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition"].pop(0)
                    simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition_status"].pop(0)
            #print(simulation.EXECUTION_PATH_TREE)
            #print(simulation.SYM_PATH_CONDITIONS_AND_VARS)
            cont_concolic = True
            while(True):
                find_new_path_trace()
                trace = NEXT_TRACE
                #print("TRACE --> " + str(trace))
                NEXT_TRACE = []
                if(trace == []):
                    cont_concolic = False
                    break
                found = reset_and_set_initials(trace, number_of_pars, hex_f_id)
                if(found == "sat"):
                    break
            if(cont_concolic == False or remaining_run == 0):
                break
        print("\n")
        ###     BEGIN TIMESTAMP BUG CHECK   ###
        test_var = ""
        if(len(simulation.TIMESTAMP_RESULTS) > 0):
            test_var = simulation.TIMESTAMP_RESULTS[0]
        for sent_ether in simulation.TIMESTAMP_RESULTS:
            if(str(test_var) != str(sent_ether)):
                simulation.CONCOLIC_RESULTS.append({"function": str(hex_f_id), "warning": "TIMESTAMP DEPENDENCY BUG"})
                break
        simulation.TIMESTAMP_RESULTS = []
        ###     END TIMESTAMP BUG CHECK     ###

        ###     BEGIN BLOCKNUMBER BUG CHECK   ###
        test_var = ""
        if (len(simulation.BLOCKNUMBER_RESULTS) > 0):
            test_var = simulation.BLOCKNUMBER_RESULTS[0]
        for sent_ether in simulation.BLOCKNUMBER_RESULTS:
            if (str(test_var) != str(sent_ether)):
                simulation.CONCOLIC_RESULTS.append({"function": str(hex_f_id), "warning": "BLOCKNUMBER DEPENDENCY BUG"})
                break
        simulation.BLOCKNUMBER_RESULTS = []
        ###     END BLOCKNUMBER BUG CHECK     ###
    #print(simulation.STORAGE_PLACES)
    #print(simulation.STORAGE_UPDATABLE_AT)
    #print(simulation.STORAGE_IF_CONDITIONAL_SENDS)
    ###     BEGIN TOD BUG CHECK     ###
    #DIRECT DEPENDANT PART
    for storage in simulation.STORAGE_PLACES:
        if storage in simulation.STORAGE_UPDATABLE_AT.keys():
            f_ids = simulation.STORAGE_UPDATABLE_AT[storage]
            f_to_val = {}   #f_id -> values([])
            for one in simulation.STORAGE_DIRECT_DEPENDANT_SENDS:
                if storage in one["cond_storages"]:
                    if one["function"] in f_to_val.keys():
                        f_to_val[one["function"]].append(one["value"])
                    else:
                        f_to_val[one["function"]] = [one["value"]]
            for function in f_to_val.keys():
                for up_func in simulation.STORAGE_UPDATABLE_AT[storage]:
                    if(up_func != function):
                        simulation.CONCOLIC_RESULTS.append(
                            {"function": str(function), "warning": "TOD DEPENDENCY BUG with STORAGE_" + str(storage)})
                        break
    #IF CONDITIONAL PART
    for storage in simulation.STORAGE_PLACES:
        if storage in simulation.STORAGE_UPDATABLE_AT.keys():
            f_ids = simulation.STORAGE_UPDATABLE_AT[storage]
            f_to_val = {}   #f_id -> values([])
            for one in simulation.STORAGE_IF_CONDITIONAL_SENDS:
                if storage in one["cond_storages"]:
                    if one["function"] in f_to_val.keys():
                        f_to_val[one["function"]].append(one["value"])
                    else:
                        f_to_val[one["function"]] = [one["value"]]
            for function in f_to_val.keys():
                for up_func in simulation.STORAGE_UPDATABLE_AT[storage]:
                    if(up_func != function):
                        all_same = True
                        first_val = ""
                        if(len(f_to_val[function]) > 0):
                            first_val = f_to_val[function][0]
                        for val in f_to_val[function]:
                            if val != first_val:
                                all_same = False
                                break
                        if(all_same == False):
                            simulation.CONCOLIC_RESULTS.append(
                                {"function": str(function),
                                 "warning": "TOD DEPENDENCY BUG with STORAGE_" + str(storage)})
                            break
    ###     END TOD BUG CHECK     ###
    # STORAGE_PLACES = []  # Each element --> "1"
    # STORAGE_UPDATABLE_AT = {}  # Each element ---> "1" : ["0x12323", "0x23222"]
    # STORAGE_IF_CONDITIONAL_SENDS = []  # Each element ---> "function" : "$function_id", "cond_storages" : ["1", "2"], "value" : "$value"
    # STORAGE_DIRECT_DEPENDANT_SENDS = []  # Each element ---> "function" : "$function_id", "cond_storages" : ["1", "2"], "value" : "$value"

    #print(simulation.CONCOLIC_RESULTS)
    TIMESTAMP_DETECTION = False
    MISHANDLED_EXCEPTION_DETECTION = False
    REENTRANCY_DETECTION = False
    BLOCKNUMBER_DETECTION = False
    TOD_DETECTION = False
    for res in simulation.CONCOLIC_RESULTS:
        if (res["warning"] == "TIMESTAMP DEPENDENCY BUG"):
            TIMESTAMP_DETECTION = True
        elif (res["warning"] == "MISHANDLED EXCEPTION BUG"):
            MISHANDLED_EXCEPTION_DETECTION = True
        elif (res["warning"] == "REENTRANCY BUG"):
            REENTRANCY_DETECTION = True
        elif (res["warning"] == "BLOCKNUMBER DEPENDENCY BUG"):
            BLOCKNUMBER_DETECTION = True
        else:
            TOD_DETECTION = True
    err_count = 0
    for opc_name in FILE_OPCODES:
        if(opc_name.name == "ERROR"):
            err_count += 1
    print("\n\n ####   RESULTS   ###")
    if not (TIMESTAMP_DETECTION or MISHANDLED_EXCEPTION_DETECTION or REENTRANCY_DETECTION or BLOCKNUMBER_DETECTION or TOD_DETECTION):
        print("THERE IS NO DETECTION OF WARNING")
    print(("CODE COVERAGE = %.2f" % ((100.0*len(CODE_COVERAGE))/(len(FILE_PC_OPCODES)-err_count))) + "%")
    if (TIMESTAMP_DETECTION):
        print("TIMESTAMP DEPENDENCY DETECTED")
    if (BLOCKNUMBER_DETECTION):
        print("BLOCKNUMBER DEPENDENCY DETECTED")
    if (MISHANDLED_EXCEPTION_DETECTION):
        print("MISHANDLED EXCEPTION DETECTED")
    if (REENTRANCY_DETECTION):
        print("REENTRANCY DETECTED")
    if (TOD_DETECTION):
        print("TRANSACTION-ORDERING DEPENDENCE(TOD) DETECTED")

if __name__ == '__main__':
    main()

"""
    print("STACK ---> " + str(simulation.STACK))
    print("SYM_STACK ---> " + str(simulation.SYM_STACK))
    print("MEMORY ---> " + str(simulation.MEMORY))
    print("SYM_MEMORY ---> " + str(simulation.SYM_MEMORY))
    print("STORAGE ---> " + str(simulation.STORAGE))
    print("SYM_STORAGE ---> " + str(simulation.SYM_STORAGE))
    print("SYM_PATH_CONDITIONS_AND_VARS ---> " + str(simulation.SYM_PATH_CONDITIONS_AND_VARS))
    print(simulation.GLOBAL_STATE)
    print(len(simulation.STACK) == len(simulation.SYM_STACK))
    print(simulation.EXECUTION_PATH_TREE)
"""
"""
    Solver_t = Solver()
    Solver_t.add(simulation.SYM_PATH_CONDITIONS_AND_VARS["path_condition"][0] == True)
    Solver_t.check()
    model = Solver_t.model()
    print(model)
"""
"""
    simulation.MEMORY[0] = "2a"
    simulation.MEMORY[1] = "33"
    simulation.MEMORY[2] = "00"
    simulation.MEMORY[3] = "22"
    simulation.MEMORY[4] = "2a"
    simulation.MEMORY[5] = "33"
    simulation.MEMORY[6] = "00"
    simulation.MEMORY[7] = "22"
    simulation.MEMORY[8] = "2a"
    simulation.MEMORY[9] = "33"
    simulation.MEMORY[10] = "00"
    simulation.MEMORY[11] = "22"
    simulation.MEMORY[12] = "2a"
    simulation.MEMORY[13] = "33"
    simulation.MEMORY[14] = "00"
    simulation.MEMORY[15] = "22"
    simulation.MEMORY[16] = "2a"
    simulation.MEMORY[17] = "33"
    simulation.MEMORY[18] = "00"
    simulation.MEMORY[19] = "22"
    simulation.MEMORY[20] = "2a"
    simulation.MEMORY[21] = "33"
    simulation.MEMORY[22] = "00"
    simulation.MEMORY[23] = "22"
    simulation.MEMORY[24] = "2a"
    simulation.MEMORY[25] = "33"
    simulation.MEMORY[26] = "00"
    simulation.MEMORY[27] = "22"
    simulation.MEMORY[28] = "2a"
    simulation.MEMORY[29] = "33"
    simulation.MEMORY[30] = "00"
    simulation.MEMORY[31] = "22"
    simulation.MEMORY[32] = "2a"
    simulation.MEMORY[33] = "33"
    simulation.MEMORY[34] = "00"
    simulation.MEMORY[35] = "22"
    simulation.MEMORY[36] = "2a"
    simulation.MEMORY[37] = "33"
    simulation.MEMORY[38] = "00"
    simulation.MEMORY[39] = "22"
    simulation.MEMORY[40] = "2a"
    simulation.MEMORY[41] = "33"
    simulation.MEMORY[42] = "00"
    simulation.MEMORY[43] = "22"
    simulation.MEMORY[44] = "2a"
    simulation.MEMORY[45] = "33"
    simulation.MEMORY[46] = "00"
    simulation.MEMORY[47] = "22"

    simulation.STORAGE["222"] = "333"

    simulation.GLOBAL_STATE["pc"] = 881
    print(simulation.GLOBAL_STATE["pc"])
    x = z3.BitVec('x', 256)
    y = z3.BitVec('y', 256)
    z = z3.BitVec('z', 256)
    simulation.SYM_STACK.append(x - 5)
    simulation.SYM_STACK.append(2)
    simulation.SYM_STACK.append(3)
    simulation.SYM_STACK.append(z)
    simulation.SYM_STACK.append(33)
    simulation.SYM_STACK.append(x)
    simulation.symbolic_execute_opcode("MSTORE8", FILE_OPCODES, FILE_PC_OPCODES)
    #simulation.symbolic_execute_opcode("SDIV", FILE_OPCODES, FILE_PC_OPCODES)

    print("SYM_STACK ---> " + str(simulation.SYM_STACK))
    #simulation.STACK.append(str(int("0x4ff2588fF42954bB45127aD4805099796756aCf5",16)))
    #simulation.execute_opcode("SUICIDE", FILE_OPCODES, FILE_PC_OPCODES)
    #print("STACK ---> " + str(simulation.STACK))
    #print("MEMORY --> " + str(simulation.MEMORY))
    #print("STORAGE -> " + str(simulation.STORAGE))
    #print("PC ------> " + str(simulation.GLOBAL_STATE["pc"]))
    #print(simulation.CONTRACT_PROPERTIES["Ia"]["balance"])
    #print(simulation.CONTRACT_PROPERTIES["Is"]["balance"])

    a1 = z3.BitVec('x', 256)
    a2 = z3.BitVec('y', 256)
    a3 = z3.BitVec('z', 256)
    a4 = z3.BitVec('t', 256)
    print(simulation.SYM_PATH_CONDITIONS_AND_VARS)

    t = simulation.SYM_STACK.pop()
    ss = Solver()
    ss.add(t == 1)
    print(ss.check())
    model = ss.model()
    print(model)

    print(2**255)
    print(2**256)
    xxx = int(str(model[x]))
    s_xxx = simulation.to_signed(xxx)
    yyy = int(str(model[y]))
    s_yyy = simulation.to_signed(yyy)
    #zzz = int(str(model[z]))
    #s_zzz = simulation.to_signed(zzz)
    print("X --> " + str(xxx))
    print("X --> " + str(s_xxx))
    print("Y --> " + str(yyy))
    print("Y --> " + str(s_yyy))
    #print("Z --> " + str(zzz))
    #print("Z --> " + str(s_zzz))
    #print((xxx*yyy)%zzz)
"""

"""
    simulation.CONTRACT_PROPERTIES['exec']['calldata'] = "0xa3af609b"
    for a in range(40):
        op_name = FILE_OPCODES[FILE_PC_TO_INDEX[simulation.GLOBAL_STATE["pc"]]].name
        if (op_name == "RETURN" or op_name == "REVERT" or op_name == "STOP"):
            break
        simulation.symbolic_execute_opcode(op_name, FILE_OPCODES, FILE_PC_OPCODES)
        simulation.execute_opcode(op_name, FILE_OPCODES, FILE_PC_OPCODES)
    print("STACK ---> " + str(simulation.STACK))
    print("SYM_STACK ---> " + str(simulation.SYM_STACK))
    print("STORAGE ---> " + str(simulation.STORAGE))
    print("SYM_STORAGE ---> " + str(simulation.SYM_STORAGE))
    print("SYM_PATH_CONDITIONS_AND_VARS ---> " + str(simulation.SYM_PATH_CONDITIONS_AND_VARS))
    print(simulation.GLOBAL_STATE)
    print(len(simulation.STACK) == len(simulation.SYM_STACK))
    print(simulation.EXECUTION_PATH_TREE)
"""

"""
395  solc --opcodes asd.sol 
  396  solc --bin-runtime asd.sol > bin.txt
  397  python3
  398  python3
  399  clear
  400  solc --bin-runtime asd.sol > bin.txt
  401  solc --bin-runtime asd.sol > bin.txt
  402  solc --bin-runtime asd.sol > bin.txt
  403  solc --bin-runtime asd.sol > bin.txt
  404  solc --bin asd.sol > bin.txt
  405  solc --bin --optimize asd.sol > bin.txt
  406  solc --bin --optimize asd.sol > bin.txt
  407  solc --bin --optimize asd.sol > bin.txt
  408  solc --bin asd.sol > bin.txt
  409  solc --bin --optimize asd.sol > bin.txt
  410  solc --bin asd.sol > bin.txt
  411  solc --bin --optimize asd.sol > bin.txt
  412  solc --bin --optimize asd.sol > bin.txt
  413  solc --bin --optimize asd.sol > bin.txt
  414  solc --bin --optimize asd.sol > bin.txt
  415  solc --bin asd.sol > bin.txt
  416  solc --bin asd.sol > bin.txt
  417  solc --bin asd.sol > bin.txt
  418  solc --bin asd.sol > bin.txt
  419  solc --bin asd.sol > bin.txt
  420  solc --bin asd.sol > bin.txt
  421  solc --bin asd.sol > bin.txt
  422  python3
  423  python3
  424  solc --bin-runtime asd.sol > bin.txt
  425  solc --bin asd.sol > bin.txt
  426  solc --abi asd.sol 
  427  solc --hashes asd.sol 
  428  solc --bin asd.sol > bin.txt
  429  solc --bin asd.sol > bin.txt
  430  python3
  431  ls
  432  solc
  433  solc --bin asd.sol > bin.txt
  434  solc --bin asd.sol > bin.txt
  435  solc --bin asd.sol > bin.txt
  436  solc --bin asd.sol > bin.txt
  437  solc --bin asd.sol > bin.txt
  438  solc --bin asd.sol > bin.txt
  439  solc --bin asd.sol > bin.txt
  440  solc --bin asd.sol > bin.txt
  441  evm disasm asd.sol 
  442  solc --bin asd.sol > bin.txt
  443  solc --bin asd.sol > bin.txt
  444  solc --bin asd.sol > bin.txt
  445  solc --bin asd.sol > bin.txt
  446  evm diasm asd.sol 
  447  evm disasm asd.sol 
  448  solc --opcode asd.sol 
  449  solc --opcodes asd.sol 
  450  solc --bin asd.sol > bin.txt
  451  solc --bin asd.sol > bin.txt
  452  solc --bin asd.sol > bin.txt
  453  solc --bin asd.sol > bin.txt
  454  solc --bin asd.sol > bin.txt
  455  solc --bin asd.sol > bin.txt
  456  solc --bin asd.sol > bin.txt
  457  solc --bin asd.sol > bin.txt
  458  solc --bin asd.sol > bin.txt
  459  solc --bin asd.sol > bin.txt
  460  solc --bin asd.sol > bin.txt
  461  evm disasm asd.sol 
  462  solc --opcodes asd.sol 
  463  solc
  464  solc --ast asd.sol 
  465  solc
  466  solc --asm asd.sol 
  467  solc
  468  solc --asm-json asd.sol 
  469  solc
  470  solc --asm asd.sol 
  471  solc
  472  solc --bin asd.sol > bin.txt
  473  solc --bin asd.sol > bin.txt
  474  solc --opcodes asd.sol 
  475  solc --bin asd.sol > bin.txt
  476  solc --bin asd.sol > bin.txt
  477  solc --bin asd.sol > bin.txt
  478  evm disasm
  479  evm
  480  evm run asd.sol 
  481  solc asd.sol 
  482  solc --bin asd.sol > bin.txt
  483  solc --bin asd.sol > bin.txt
  484  ls
  485  cd oyente/
  486  ls
  487  cd oyente/
  488  ls
  489  solc --bin--runtime asd.sol > bin.txt
  490  solc --bin-runtime asd.sol > bin.txt
  491  solc --bin-runtime asd.sol > bin.txt
  492  cd ..
  493  cd ..
  494  ls
  495  solc --bin-runtime asd.sol > bin.txt
  496  ls
  497  evm disasm bin.txt 
  498  evm disasm bin.txt 
  499  solc --bin-runtime asd.sol > bin.txt

"""
