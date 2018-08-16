import math
import random

inBuff = open('envInput', 'r')
outBuff = open('envOutput', 'w')

num_strats = 17
num_rounds = 24

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

#This is just a 0-cost vector for n strats
def dummyVector (n) :
    return [0.0] * n
#This is a random cost vector for n strats
def dummyVector2 (n) :
    return [random.uniform(-1,1) for _ in range(n)]

#This is a .5 cost vector for all strats except the first 
def dummyVector3 (n) :
    l = [0.5] * n
    l[0] = .25 
    print(l)
    return l

for x in range(num_rounds):
    print ("Starting round: " + str(x))
    weightVec_string = inBuff.readline()
    print(weightVec_string)
    costVec = dummyVector2(num_strats)
    outBuff.write(
        stringOfDyadicList(
            floatListToDyadic(costVec)))
    outBuff.flush()
