"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
*                                                               *
*                          envProc.py                           *
*                                                               *
* Filename: envProc.py                                          *
*                                                               *
* Description: This file implements an environment for the      *
*              verified MWU client to implement a linear        *
*              classifier. This program generates a random      *
*              example set and generates gain vectors           *
*              for MWU to use as the set is classified.         *
*              Upon complete classification, the program also   *
*              runs an implementation fully in Python for       *
*              comparison and research purposes.                *
*                                                               *
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

import random
import numpy
import matplotlib
import matplotlib.pyplot as plt
import math
from Classifier_Environment import Classifier_Environment
from Classifier import Classifier

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
*                                                               *
*                     FUNCTION DEFINTION                        *
*                                                               *
* Name: generate_seperable_set                                  *
*                                                               *
* Purpose: This function creates a set of 100 examples of       *
*          random dimension in set [1,50]. This is a set with   *
*          a large margin solution as each example can be       *
*          classified by the randomly generated hyperplane      *
*          created within the function. It then returns this    *
*          set with the epsilon and hyperplane used as follows: *
*          (examples, epsilon, target).                         *
*                                                               *
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
def generate_seperable_set(dimension, num_examples):
    #Generate a random hyperplane
    target = []
    count = dimension
    while count > 0:
        #Append target with a random value in range [0,1)
        target.append(random.random())
        count -= 1


    #Normalize random hyperplance
    total = 0
    for i in range(0, dimension):
        total += target[i]
    for i in range(0, dimension):
        target[i] /= total


    #Generate set of 100 examples that are classifiable to generated target
    examples = []

    #Set random epsilon value in range (0,1)
    epsilon = 0
    while epsilon == 0: #Make sure zero doesn't get chosen
        epsilon = random.random() #Make random number in [0,1)


    for i in range (0, num_examples):
        is_large_margin = False
        count = 0 #Keep track if loop is taking too many tries
        while is_large_margin == False:
            vector = []
            for j in range (0, dimension):
                #Append random float of 3 decimals between (-1,1)
                vector.append(round(2*random.random()-1, 3))

            if abs(numpy.dot(vector, target)) >= epsilon:
                is_large_margin = True

            if count >= 1000:
                return generate_seperable_set(dimension, num_examples)

            count += 1

        if numpy.dot(vector, target) >= epsilon:
            label = 1
        else:
            label = -1

        examples.append((vector, label))

    return (examples, epsilon, target)



"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
*                                                               *
*                     FUNCTION DEFINTION                        *
*                                                               *
* Name: run_python_classifier                                   *
*                                                               *
* Purpose: This function takes a generated example set and      *
*          epsilon value and runs the standalone python         *
*          implementation of the linear classifier with MWU in  *
*          the file Classifier.py and then outputs data on its  *
*          performance.                                         *
*                                                               *
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
def run_python_classifier(control):
    print "Commencing Python Test ..."
    max = control.upper_bound
    print "Number Correct Initially: ", control.num_correctly_classified()
    print "Max Rounds: ", max
    control.fully_classify(max)
    print "Rounds Taken: ", control.rounds
    assert control.rounds <= max
    print "Number Correct After: ", control.num_correctly_classified()



"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
                              MAIN
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
inBuff = open('envInput', 'r')
outBuff = open('envOutput', 'w')

num_rounds = 80
num_strats = 10
num_examples = 20

#Get nontrivial example set (not all correct initially)
all_correct_initially = True
while all_correct_initially == True:
    generated_set = generate_seperable_set(num_strats, num_examples)
    examples = generated_set[0]
    epsilon = generated_set[1]

    experiment = Classifier_Environment(examples, epsilon)
    control = Classifier(examples, epsilon)
    if experiment.num_correctly_classified() < num_examples:
        all_correct_initially = False

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

for x in range(1, num_rounds + 1):
    print ("Starting round: " + str(x))
    weightVec_string = inBuff.readline()

    experiment.set_target(weightVec_string)
    gain_vector = experiment.generate_gain_vector()

    if experiment.is_classified_flag == True:
        print "Fully Classified!"
        run_python_classifier(control)
        exit()

    dyadic_gain_list = floatListToDyadic(gain_vector)
    dyadic_gain_string = stringOfDyadicList(dyadic_gain_list)
    print "Current Weight Vector: ", weightVec_string
    print "Calculated Gain Vector: ", dyadic_gain_string

    outBuff.write(dyadic_gain_string)
    outBuff.flush()
