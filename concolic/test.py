import sha3
from web3 import Web3
import web3
import pybase64
from ethereum_data import *
import helper
from z3 import *
import six

k = 115792089237316195423570985008687907853269984665640564039457584007913129639936
f = k + 6
s = 1
UNSIGNED_BOUND_NUMBER = 2**256 - 1
NEGATIVE_BOUND_NUMBER = 2**256
BYTE_BOUND_NUMBER = 2**8 -1
def to_unsigned(num):
    if(num < 0):
        return num + (2**256)
    return num

def to_signed(num):
    if(num >= (2**255)):
        return num - (2**256)
    return num

def formed(num):
    if(num < 0):
        return NEGATIVE_BOUND_NUMBER + num
    return num
"""
k = BitVec('k',8)
l = BitVec('l',8)
m = BitVec('m',8)

x = Int('x')
y = Int('y')

s = Solver()
print(s)

s.add(x > 10, y == x + 2)
print (s)
print ("Solving constraints in the solver s ...")
print (s.check())

s.push()
s.add(y < 11)
s.add(y >2)
s.pop()

print(s)
"""

z3_abs = lambda x: If(x >= 0, 2*x, -x + 3)
k = z3_abs(12)
print(k)

a = BitVecVal(17,4)
print(a)

k = BitVecVal(1,14)
l = BitVecVal(3,14)
print(simplify(k+3))



"""
k = EthereumData()
lo = k.getCode("0xb342354cbe6db5823a0b00365ff1ec3ab05f129d")
print(lo)
print(lo[3:])

# .decode('utf-8', 'strict')
a = Web3.sha3(text=u'I♥SF')
b = b'\xff\xf8\x00\x00\x00\x00\x00\x00'

k = "asd"
l = k.encode('utf-8', 'strict')
m = Web3.sha3(7633012)
n = Web3.toHex(m)
print(m)
print(n)

c = Web3.sha3(b'\x74\x78\x74')
#print(Web3.toHex(c))

#d = c.decode('utf-8', 'strict')
#print(d)
"""
