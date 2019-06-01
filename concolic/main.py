import shlex
import subprocess
import os
import re
import opcodes
import basicblock


class OPCODE:
	def __init__(self, name, par):
		self.name = name
		self.par = par


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
		if (opc.name in separators):
			dest = []
			if(opc.name == 'JUMP' and re.search('PUSH*',FILE_OPCODES[opc_number-1].name)):
				dest.append(FILE_OPCODES[opc_number-1].par)
			elif(opc.name == 'JUMPI' and re.search('PUSH*',FILE_OPCODES[opc_number-1].name)):
				dest.append(FILE_OPCODES[opc_number - 1].par)
				dest.append(FILE_PC_OPCODES[opc_number]+1)
			pc = FILE_PC_OPCODES[opc_number]
			basic_blocks.append(basicblock.BasicBlock(init_pc, pc, opc.name, dest))
			init_pc = FILE_PC_OPCODES[opc_number+1]
	return basic_blocks

"""
solc --bin-runtime asd.sol > bin.txt
solc --optimize --opcodes asd.sol 
"""
def main():

	f = open('bin.txt', 'r')
	bin_file = f.read()
	f.close()
	index = bin_file.index('part:')
	bin_file = bin_file[index + 7:]

	FILE_OPCODES, FILE_PC_OPCODES = get_opcodes(bin_file)
	for a in range(len(FILE_PC_OPCODES)):
		FILE_PC_OPCODES[a] = int(FILE_PC_OPCODES[a])

	for a in range(len(FILE_OPCODES)):
		print( "[" + str(FILE_PC_OPCODES[a]) + "]" + " " +FILE_OPCODES[a].name + "  " + str(FILE_OPCODES[a].par))

	print(len(FILE_PC_OPCODES))
	print(len(FILE_OPCODES))

	basic_blocks = find_basic_blocks(FILE_OPCODES, FILE_PC_OPCODES)
	for i in basic_blocks:
		print(str(i.start) + " <-> " + str(i.end) + " <-> " + i.termination + " <-> " + str(i.targets))

if __name__ == '__main__':
	main()


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