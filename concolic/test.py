k = 115792089237316195423570985008687907853269984665640564039457584007913129639936
f = k + 6
s = 1
UNSIGNED_BOUND_NUMBER = 2**256 - 1
NEGATIVE_BOUND_NUMBER = 2**256
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


print((~3) & UNSIGNED_BOUND_NUMBER)


