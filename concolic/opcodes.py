opcodes = {
    '00' : 'STOP',
    '01' : 'ADD',
    '02' : 'MUL',
    '03' : 'SUB',
    '04' : 'DIV',
    '05' : 'SDIV',
    '06' : 'MOD',
    '07' : 'SMOD',
    '08' : 'ADDMOD',
    '09' : 'MULMOD',
    '0a' : 'EXP',
    '0b' : 'SIGNEXTEND',
    '10' : 'LT',
    '11' : 'GT',
    '12' : 'SLT',
    '13' : 'SGT',
    '14' : 'EQ',
    '15' : 'ISZERO',
    '16' : 'AND',
    '17' : 'OR', # 'EVMOR'
    '18' : 'XOR',
    '19' : 'NOT',
    '1a' : 'BYTE',
    '20' : 'KECCAK256', # 'SHA3'
    '30' : 'ADDRESS',
    '31' : 'BALANCE',
    '32' : 'ORIGIN',
    '33' : 'CALLER',
    '34' : 'CALLVALUE',
    '35' : 'CALLDATALOAD',
    '36' : 'CALLDATASIZE',
    '37' : 'CALLDATACOPY',
    '38' : 'CODESIZE',
    '39' : 'CODECOPY',
    '3a' : 'GASPRICE',
    '3b' : 'EXTCODESIZE',
    '3c' : 'EXTCODECOPY',
    '40' : 'BLOCKHASH',
    '41' : 'COINBASE',
    '42' : 'TIMESTAMP',
    '43' : 'NUMBER',
    '44' : 'DIFFICULTY',
    '45' : 'GASLIMIT',
    '50' : 'POP',
    '51' : 'MLOAD',
    '52' : 'MSTORE',
    '53' : 'MSTORE8',
    '54' : 'SLOAD',
    '55' : 'SSTORE',
    '56' : 'JUMP',
    '57' : 'JUMPI',
    '58' : 'PC',
    '59' : 'MSIZE',
    '5a' : 'GAS',
    '5b' : 'JUMPDEST',
    '60' : 'PUSH1',
    '61' : 'PUSH2',
    '62' : 'PUSH3',
    '63' : 'PUSH4',
    '64' : 'PUSH5',
    '65' : 'PUSH6',
    '66' : 'PUSH7',
    '67' : 'PUSH8',
    '68' : 'PUSH9',
    '69' : 'PUSH10',
    '6a' : 'PUSH11',
    '6b' : 'PUSH12',
    '6c' : 'PUSH13',
    '6d' : 'PUSH14',
    '6e' : 'PUSH15',
    '6f' : 'PUSH16',
    '70' : 'PUSH17',
    '71' : 'PUSH18',
    '72' : 'PUSH19',
    '73' : 'PUSH20',
    '74' : 'PUSH21',
    '75' : 'PUSH22',
    '76' : 'PUSH23',
    '77' : 'PUSH24',
    '78' : 'PUSH25',
    '79' : 'PUSH26',
    '7a' : 'PUSH27',
    '7b' : 'PUSH28',
    '7c' : 'PUSH29',
    '7d' : 'PUSH30',
    '7e' : 'PUSH31',
    '7f' : 'PUSH32',
    '80' : 'DUP1',
    '81' : 'DUP2',
    '82' : 'DUP3',
    '83' : 'DUP4',
    '84' : 'DUP5',
    '85' : 'DUP6',
    '86' : 'DUP7',
    '87' : 'DUP8',
    '88' : 'DUP9',
    '89' : 'DUP10',
    '8a' : 'DUP11',
    '8b' : 'DUP12',
    '8c' : 'DUP13',
    '8d' : 'DUP14',
    '8e' : 'DUP15',
    '8f' : 'DUP16',
    '90' : 'SWAP1',
    '91' : 'SWAP2',
    '92' : 'SWAP3',
    '93' : 'SWAP4',
    '94' : 'SWAP5',
    '95' : 'SWAP6',
    '96' : 'SWAP7',
    '97' : 'SWAP8',
    '98' : 'SWAP9',
    '99' : 'SWAP10',
    '9a' : 'SWAP11',
    '9b' : 'SWAP12',
    '9c' : 'SWAP13',
    '9d' : 'SWAP14',
    '9e' : 'SWAP15',
    '9f' : 'SWAP16',
    'a0' : 'LOG0',
    'a1' : 'LOG1',
    'a2' : 'LOG2',
    'a3' : 'LOG3',
    'a4' : 'LOG4',
    'f0' : 'CREATE',
    'f1' : 'CALL',
    'f2' : 'CALLCODE',
    'f3' : 'RETURN',
    'f4' : 'DELEGATECALL',
    'f5' : 'CALLBLACKBOX',
    'fa' : 'STATICCALL',
    'fd' : 'REVERT',
    'fe' : 'INVALID',
    'ff' : 'SUICIDE',
#   'ff' : 'SELFDESTRUCT'
}

op_param = {
    'STOP' : '0',
    'ADD' : '0',
    'MUL' : '0',
    'SUB' : '0',
    'DIV' : '0',
    'SDIV' : '0',
    'MOD' : '0',
    'SMOD' : '0',
    'ADDMOD' : '0',
    'MULMOD' : '0',
    'EXP' : '0',
    'SIGNEXTEND' : '0',
    'LT' : '0',
    'GT' : '0',
    'SLT' : '0',
    'SGT' : '0',
    'EQ' : '0',
    'ISZERO' : '0',
    'AND' : '0',
    'OR' : '0', # 'EVMOR'
    'XOR' : '0',
    'NOT' : '0',
    'BYTE' : '0',
    'KECCAK256' : '0', # 'SHA3'
    'ADDRESS' : '0',
    'BALANCE' : '0',
    'ORIGIN' : '0',
    'CALLER' : '0',
    'CALLVALUE' : '0',
    'CALLDATALOAD' : '0',
    'CALLDATASIZE' : '0',
    'CALLDATACOPY' : '0',
    'CODESIZE' : '0',
    'CODECOPY' : '0',
    'GASPRICE' : '0',
    'EXTCODESIZE' : '0',
    'EXTCODECOPY' : '0',
    'BLOCKHASH' : '0',
    'COINBASE' : '0',
    'TIMESTAMP' : '0',
    'NUMBER' : '0',
    'DIFFICULTY' : '0',
    'GASLIMIT' : '0',
    'POP' : '0',
    'MLOAD' : '0',
    'MSTORE' : '0',
    'MSTORE8' : '0',
    'SLOAD' : '0',
    'SSTORE' : '0',
    'JUMP' : '0',
    'JUMPI' : '0',
    'PC' : '0',
    'MSIZE' : '0',
    'GAS' : '0',
    'JUMPDEST' : '0',
    'PUSH1' : '2',
    'PUSH2' : '4',
    'PUSH3' : '6',
    'PUSH4' : '8',
    'PUSH5' : '10',
    'PUSH6' : '12',
    'PUSH7' : '14',
    'PUSH8' : '16',
    'PUSH9' : '18',
    'PUSH10' : '20',
    'PUSH11' : '22',
    'PUSH12' : '24',
    'PUSH13' : '26',
    'PUSH14' : '28',
    'PUSH15' : '30',
    'PUSH16' : '32',
    'PUSH17' : '34',
    'PUSH18' : '36',
    'PUSH19' : '38',
    'PUSH20' : '40',
    'PUSH21' : '42',
    'PUSH22' : '44',
    'PUSH23' : '46',
    'PUSH24' : '48',
    'PUSH25' : '50',
    'PUSH26' : '52',
    'PUSH27' : '54',
    'PUSH28' : '56',
    'PUSH29' : '58',
    'PUSH30' : '60',
    'PUSH31' : '62',
    'PUSH32' : '64',
    'DUP1' : '0',
    'DUP2' : '0',
    'DUP3' : '0',
    'DUP4' : '0',
    'DUP5' : '0',
    'DUP6' : '0',
    'DUP7' : '0',
    'DUP8' : '0',
    'DUP9' : '0',
    'DUP10' : '0',
    'DUP11' : '0',
    'DUP12' : '0',
    'DUP13' : '0',
    'DUP14' : '0',
    'DUP15' : '0',
    'DUP16' : '0',
    'SWAP1' : '0',
    'SWAP2' : '0',
    'SWAP3' : '0',
    'SWAP4' : '0',
    'SWAP5' : '0',
    'SWAP6' : '0',
    'SWAP7' : '0',
    'SWAP8' : '0',
    'SWAP9' : '0',
    'SWAP10' : '0',
    'SWAP11' : '0',
    'SWAP12' : '0',
    'SWAP13' : '0',
    'SWAP14' : '0',
    'SWAP15' : '0',
    'SWAP16' : '0',
    'LOG0' : '0',
    'LOG1' : '0',
    'LOG2' : '0',
    'LOG3' : '0',
    'LOG4' : '0',
    'CREATE' : '0',
    'CALL' : '0',
    'CALLCODE' : '0',
    'RETURN' : '0',
    'DELEGATECALL' : '0',
    'CALLBLACKBOX' : '0',
    'STATICCALL' : '0',
    'REVERT' : '0',
    'INVALID' : '0',
    'SUICIDE' : '0',
#   'ff' : 'SELFDESTRUCT'
}

byte_values = {
    '0' : 0,
    '255': 1,
    '65535': 2,
    '16777215': 3,
    '4294967295': 4,
    '1099511627775': 5,
    '281474976710655': 6,
    '72057594037927935': 7,
    '18446744073709551615': 8,
    '4722366482869645213695': 9,
    '1208925819614629174706175': 10,
    '309485009821345068724781055': 11,
    '79228162514264337593543950335': 12,
    '20282409603651670423947251286015': 13,
    '5192296858534827628530496329220095': 14,
    '1329227995784915872903807060280344575': 15,
    '340282366920938463463374607431768211455': 16,
    '87112285931760246646623899502532662132735': 17,
    '22300745198530623141535718272648361505980415': 18,
    '5708990770823839524233143877797980545530986495': 19,
    '1461501637330902918203684832716283019655932542975': 20,
    '374144419156711147060143317175368453031918731001855': 21,
    '95780971304118053647396689196894323976171195136475135': 22,
    '24519928653854221733733552434404946937899825954937634815': 23,
    '6277101735386680763835789423207666416102355444464034512895': 24,
    '1606938044258990275541962092341162602522202993782792835301375': 25,
    '411376139330301510538742295639337626245683966408394965837152255': 26,
    '105312291668557186697918027683670432318895095400549111254310977535': 27,
    '26959946667150639794667015087019630673637144422540572481103610249215': 28,
    '6901746346790563787434755862277025452451108972170386555162524223799295': 29,
    '1766847064778384329583297500742918515827483896875618958121606201292619775': 30,
    '452312848583266388373324160190187140051835877600158453279131187530910662655': 31,
    '115792089237316195423570985008687907853269984665640564039457584007913129639935': 32
}
"""
def cmd_exists(cmd):
	return subprocess.call("type " + cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE) == 0

def kk():

	SOURCE_FILE = "asd.sol"

	if not cmd_exists("evm disasm"):
		print ("disasm is missing. Please install go-ethereum and make sure disasm is in the path.")
		return

	if not cmd_exists("solc"):
		print ("solc is missing. Please install the solidity compiler and make sure solc is in the path.")
		return

	# Compile first

	solc_cmd = "solc --optimize --bin-runtime %s"

	FNULL = open(os.devnull, 'w')

	solc_p = subprocess.Popen(shlex.split(solc_cmd % SOURCE_FILE), stdout=subprocess.PIPE, stderr=FNULL)
	solc_out = solc_p.communicate()

	#print(solc_out)
	#print(solc_out[0])
	print(solc_out[0].decode('utf-8'))

	solidity_out_string = solc_out[0].decode('utf-8')

	for (cname, bin_str) in re.findall(r"\n======= (.*?) =======\nBinary of the runtime part: \n(.*?)\n", solidity_out_string):
		print ("Contract %s:" % cname)
		bin_str += "\0"
		bin_str = bin_str

		disasm_out = ""
		try:
			disasm_p = subprocess.Popen(shlex.split('evm disasm'), stdout=subprocess.PIPE, stdin=subprocess.PIPE)
			disasm_out = disasm_p.communicate(input=bin_str)[0]

		except:
			print ("Disassembly failed.")

		print(disasm_out)
		# Run symExec

with open(cname + '.evm.disasm', 'w') as of:
    of.write(disasm_out)

# TODO: Do this as an import and run, instead of shell call and hacky fix

os.system('python symExec.py %s.evm.disasm %d %d %d %d %d %d %d %d %d %d %s' % (
cname, global_params.IGNORE_EXCEPTIONS, global_params.REPORT_MODE, global_params.PRINT_MODE, global_params.DATA_FLOW,
global_params.DEBUG_MODE, global_params.CHECK_CONCURRENCY_FP, global_params.TIMEOUT, global_params.UNIT_TEST,
global_params.GLOBAL_TIMEOUT, global_params.PRINT_PATHS, cname + ".json" if args.json else ""))

if args.evm:
    with open(cname + '.evm', 'w') as of:
        of.write(bin_str)

os.system('rm %s.evm.disasm' % (cname))
"""""