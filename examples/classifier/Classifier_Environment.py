"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
*                                                               *
*                      CLASS DEFINITION                         *
*                                                               *
* Name: Classifier_Environment                                  *
*                                                               *
* Purpose: This class allows multiple instances of the MWUA     *
*          for different linear classifiers to be generated     *
*          and tested. The class essentially houses the whole   *
*          algorithm. It must be given an example set, and an   *
*          epsilon value. It then provides the functions        *
*          necessary for an environement to interface with a    *
*          verified MWU client by accepting weight vectors      *
*          to update the class' "target" and then generating    *
*          gain vectors to be returned to the client. It uses   *
*          these functions to classsify the set, complete with  *
*          functions to check the number that are classified    *
*          correctly.                                           *
*                                                               *
* Attributes: examples ---- an array of pairs where each pair   *
*                           consists of an example vector and   *
*                           its label (-1 or 1)                 *
*             epsilon ----- a constant value in range 0 to 1    *
*                           passed in from instantiation        *
*             dimension --- number of features in any example   *
*             target ------ vector updated to hold linear       *
*                           classifier by end of algorithm      *
*             rho --------- constant that is max feature in any *
*                           example after absolute value        *
*             eta --------- constant determined by epsilon and  *
*                           rho                                 *
*             rounds ------ counter for how many rounds of      *
*                           algorithm has taken place           *
*             is_                                               *
*             classified_                                       *
*             flag -------- flag that is set to True once it is *
*                           found that no more violating        *
*                           examples exist                      *
*             upper_bound - the max # of iterations needed to   *
*                           fully classify as determined by     *
*                           documenting research paper          *
*                                                               *
* Functions:  __init__                                          *
*             set_rho                                           *
*             initialize_target                                 *
*             initialize_flag                                   *
*             initialize_upper_bound                            *
*             set_target                                        *
*             find_violating_example                            *
*             generate_gain_vector                              *
*             num_correctly_classified                          *
*             plot_2D_solution                                  *
*                                                               *
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
import random
import numpy
import matplotlib
import matplotlib.pyplot as plt
import math

class Classifier_Environment:

    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: __init__                                                *
    *                                                               *
    * Purpose: This function initializes all the attributes used    *
    *          by the Classifier_Environment class. These           *
    *          attributes include the exmaples set, epsilon value,  *
    *          dimension, target vector, rho, eta, and number of    *
    *          rounds.                                              *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def __init__(self, examples, epsilon):
        self.examples = examples
        self.epsilon = epsilon
        self.dimension = len(self.examples[0][0]) #Number of components in feature vectors
        self.target = self.initialize_target()
        self.rho = self.set_rho()
        self.eta = self.epsilon/(2*self.rho) #Eta defined as epsilon/(2*rho)
        self.rounds = 0 #Initialize rounds taken to 0
        self.is_classified_flag = self.initialize_flag() #Set when classification is complete
        self.upper_bound = self.initialize_upper_bound() #Set to theoretical max rounds


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: set_rho                                                 *
    *                                                               *
    * Purpose: This function finds the rho value by finding the max *
    *          feature of each example vector after taking the      *
    *          absolute value. It then returns this rho value.      *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def set_rho(self):
        rho = self.examples[0][0][0]
        #Check each example
        for example in self.examples:
            #Check each feature in each example
            for component in example[0]:
                #If new max (after abs value) found, set rho
                if abs(component) > rho:
                    rho = abs(component)
        return rho


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: initialize_target                                       *
    *                                                               *
    * Purpose: This function return a target vector initialized to  *
    *          a normalized, equal distribution based on the        *
    *          dimension size.                                      *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def initialize_target(self):
        #Fill all components of weights as a normalized uniform distribition
        target = []
        i = self.dimension
        while i > 0:
            target.append(1.0/self.dimension)
            i -= 1
        return target


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: initialize_flag                                         *
    *                                                               *
    * Purpose: This function initializes the is_classified_flag     *
    *          by returning True if all the examples are already    *
    *          correctly classified by the initial target vector    *
    *          by using the num_correctly_classified helper         *
    *          function. Else, it return False.                     *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def initialize_flag(self):
        number_examples = len(self.examples)
        #If all examples correct, set True
        if self.num_correctly_classified() == number_examples:
            return True
        else:
            return False


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: initialize_upper_bound                                  *
    *                                                               *
    * Purpose: This function initializes the upper_bound as defined *
    *          in reasearch to require no more than the ceiling of  *
    *          (4 * rho * rho * ln(dimension))/(epsilon * epsilon)  *
    *          rounds.                                              *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def initialize_upper_bound(self):
        numerator = 4 * self.rho * self.rho * numpy.log(self.dimension)
        denominator = self.epsilon * self.epsilon
        max = int(math.ceil(numerator / denominator))
        return max


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: set_target                                              *
    *                                                               *
    * Purpose: This function updates the target vector housed by    *
    *          the class given an input from the verified MWU       *
    *          as a weight vector represented by a string of        *
    *          dyadics. This function converts these dyadics to the *
    *          floating point representation used by the class.     *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def set_target(self, weightVec_string):
        target = []

        ch_index = 0
        for i in range(0, self.dimension):
            numerator = ""
            ch = weightVec_string[ch_index]
            while ch != '#':
                numerator += ch
                ch_index += 1
                ch = weightVec_string[ch_index]

            denominator = ""
            ch_index += 1
            ch = weightVec_string[ch_index]
            while ch != ' ':
                denominator += ch
                ch_index += 1
                ch = weightVec_string[ch_index]
            ch_index += 1

            numerator = float(numerator)
            denominator = int(denominator)
            target.append(numerator/(2 ** denominator))

        self.target = target


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                     FUNCTION DEFINTION                        *
    *                                                               *
    * Name: find_violating_example                                  *
    *                                                               *
    * Purpose: This function finds a random violating example by    *
    *          testing random examples until one that is            *
    *          misclassified is found. If none are found, a check   *
    *          loop is implemented to make sure there are no        *
    *          remaining violating examples.                        *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def find_violating_example(self):
        #Test random examples up to 1000 times
        for j in range(0,1000):
            #Pick a random examples index
            i = int(math.floor(random.uniform(0, len(self.examples))))

            #Get (example vector * label) dotted with target vector
            example_times_label = numpy.dot(self.examples[i][0],self.examples[i][1])
            value = numpy.dot(example_times_label, self.target)

            #If violating, return index of example, i
            if value < 0:
                return i

        k = 0
        for example in self.examples:
            #Get (example vector * label) dotted with target vector
            example_times_label = numpy.dot(example[0],example[1])
            value = numpy.dot(example_times_label, self.target)

            #If violating, return index of example, k
            if value < 0:
                return k
            else:
                k += 1

        #Return -1 if no violating indeces were found
        return -1


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                 FUNCTION DEFINTION--ORACLE                    *
    *                                                               *
    * Name: generate_gain_vector                                    *
    *                                                               *
    * Purpose: This function finds a violating example then         *
    *          generates a gain vector according to                 *
    *          formula (-1/rho)*violating_example*label             *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def generate_gain_vector(self):
        #Get a random violating example
        violating_index = self.find_violating_example()

        #If none found, set fully classified flag and return
        if violating_index == -1:
            self.is_classified_flag = True
            return []

        #Assertion must be true no matter what round
        violating_example = self.examples[violating_index][0]
        violating_label = self.examples[violating_index][1]
        example_times_label = numpy.dot(violating_example, violating_label)
        assert ((1/self.rho)*numpy.dot(self.target, example_times_label) < 0)

        gain_vector = []
        for i in range(0, self.dimension):
            feature = self.examples[violating_index][0][i]
            label = self.examples[violating_index][1]
            gain_vector.append((-1.0/self.rho)*feature*label)
        return gain_vector


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                 HELPER FUNCTION DEFINTION                     *
    *                                                               *
    * Name: num_correctly_classified                                *
    *                                                               *
    * Purpose: This function returns the number of correctly        *
    *          classified examples in the current example set and   *
    *          target vector contained by the class.                *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def num_correctly_classified(self):
        count = 0

        #Check each example in example set
        for example in self.examples:
            #Get (example vector * label) dotted with target vector
            example_times_label = numpy.dot(example[0],example[1])
            value = numpy.dot(example_times_label, self.target)

            #If classified correctly (>= 0), increment count
            if value >= 0:
                count += 1
        return count


    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    *                                                               *
    *                 HELPER FUNCTION DEFINTION                     *
    *                                                               *
    * Name: plot_2D_solution                                        *
    *                                                               *
    * Purpose: This function, when the instance of the class is in  *
    *          2 dimensions, outputs the current linear classifier  *
    *          and all the examples in the plane for verification   *
    *          of geometrical properties.                           *
    *                                                               *
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    def plot_2D_solution(self):
        if self.dimension != 2:
            return

        #Plot each point from feature vectors
        for example in self.examples:
            if example[1] == 1:
                plt.plot(example[0][0], example[0][1], 'bo')
            else:
                plt.plot(example[0][0], example[0][1], 'rs')

        plt.axis([-1.5, 1.5, -1.5, 1.5])
        plt.grid(True)

        #Generate line perpendicular to vector from MWUA weights
        perpendicular_slope = -1*(self.target[0]/self.target[1])
        x = numpy.arange(-1.5, 1.5, 0.01)
        y = perpendicular_slope*x
        plt.plot(x,y)
        plt.plot(self.target[0], self.target[1], 'gD')
        plt.show()
        return
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
                   END CLASS CLASSIFIER_ENVIRONMENT
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
