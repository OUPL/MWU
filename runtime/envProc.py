import math

inBuff = open('envInput', 'r')
outBuff = open('envOutput', 'w')

num_rounds = 10
num_strats = 10

def floatToDyadic (x) :
    frac = float.as_integer_ratio(x)
    return (frac[0], int(math.log(frac[1], 2)))

def floatListToDyadic (l):
    return (map (floatToDyadic, l))

def stringOfDyadic (x):
    return str(x[0]) + '#' + str(x[1])

def stringOfDyadicList (l) :
    s = ""
    for x in l:
        s = s + " " + (stringOfDyadic(x))
    return s + "\n"

#This is just a 0-cost vector for n players
def dummyVector (n) :
    return [0.0] * n
    
for x in range(num_rounds):
    print ("Starting round: " + str(x))
    weightVec_string = inBuff.readline()
    costVec = dummyVector(num_strats)
    outBuff.write(
        stringOfDyadicList(
            floatListToDyadic(costVec)))
    outBuff.flush()
