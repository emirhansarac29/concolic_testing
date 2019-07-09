import sha3
from web3 import Web3
import web3
import pybase64
from ethereum_data import *

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

k = EthereumData()
lo = k.getBalance("0x52bc44d5378309EE2abF1539BF71dE1b7d7bE3b5")
print(int(lo)+1)
"""
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
