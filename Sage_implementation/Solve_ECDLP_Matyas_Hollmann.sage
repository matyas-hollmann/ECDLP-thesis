#!/usr/bin/env python
# coding: utf-8


def getNumThreads():
    import multiprocessing
    try:
        nthreads = multiprocessing.cpu_count()
    except NotImplementedError:
        nthreads = 1
    return nthreads

def printMaxMemUsage():
    import resource
    res = float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)/(1024**2)
    print("Maximum memory usage during this session was: {} MegaBytes.\n".format(res))
    return

def printResults(E, P, Q, res, orderP, m, fbs, attempts, time, gbComputed):
    print("\nResults: \nGroup: {},\n#P = {},\nP = {},\nQ = {},\nres = {},\nm = {},\nFactor base size = {},\n\
Number of attempts (#GB computed) = {},\nTotal time = {} seconds,\nTime spent computing Groebner bases \
{} seconds,\nResult is valid = {}.\n"\
      .format(E,orderP,P,Q,res,m,fbs,attempts, time, gbComputed, res*P == Q))
    printMaxMemUsage()
    sys.stdout.flush()

########################################################################################################
########################################################################################################

def construct3rdSumPoly(E):
    """
    Constructs the 3rd (Semaev) summation polynomial
    for the input elliptic curve in the short Weierstrass form.

    INPUT:

    - ``E``   - an elliptic curve in the short Weierstrass form.

    Elliptic curve E is defined by the short Weierstrass
    equation: 
    Y^2 = X^3 + A*X + B
    
    In Sage this elliptic curve can be constructed this way 
    (using the long Weierstrass equation):

    E = EllipticCurve(FF, [0,0,0,A,B])

    Coefficients ``A`` and ``B`` must be elements of the finite field ``FF``.
    
    OUTPUT: Returns the 3rd summation polynomial for the elliptic
    curve ``E``. If ``E`` is not in the short Weierstrass form,
    this function raises a TypeError exception.
    
    The summation polynomial ``smp`` in variables 
    ``x1``, ``x2``, ``x3`` over a polynomial ring FF[x1,x2,x3]. 
    ``smp(a,b,c) = 0`` if and only if there are three points on the elliptic
    curve E(A,B,FF) such that:
    
    ``+-(a,y_0) +- (b,y_1) +- (c,y_2) = E(0)``,
    where E(0) is the identity element of E(A,B,FF).

    ALGORITHM: Based on the article "New algorithm for the discrete
    logarithm problem on elliptic curves" (2015) by Igor Semaev,
    available at https://eprint.iacr.org/2015/310.pdf.

    EXAMPLES:
    
    p = 19 
    
    FF = GF(p)
    
    E = EllipticCurve(FF, [0,0,0,11,1]) 
    
    print(E)
    
    SMP3 = construct3rdSumPoly(E)
    
    print(SMP3)
    
    sage: Elliptic Curve defined by y^2 = x^3 + x + 11 over Finite Field of size 19
    
    sage: x1^2*x2^2 - 2*x1^2*x2*x3 - 2*x1*x2^2*x3 + x1^2*x3^2 
    - 2*x1*x2*x3^2 + x2^2*x3^2 - 2*x1*x2 - 2*x1*x3 - 2*x2*x3
    - 6*x1 - 6*x2 - 6*x3 + 1
    """
    if E.a1() != 0 or E.a2() != 0 or E.a3() != 0:
        raise TypeError('Provided elliptic curve is not in the short Weierstrass form.') 
    
    FF = E.base_field()
    A = E.a4()
    B = E.a6()
    PR.<s1, s2, s3> = PolynomialRing(FF, 3, order='degrevlex')
    smp = (s1 - s2)**2*s3**2 - 2*((s1 + s2)*(s1*s2 + A) + 2*B)*s3 + (s1*s2 - A)**2 - 4*B*(s1 + s2)
    return smp

########################################################################################################
########################################################################################################

def calcFactorBaseSize(orderP, m):
    """
    Returns the optimal factor base size as mentioned in https://eprint.iacr.org/2017/609.pdf.
    
    INPUT:

    - ``orderP`` - order of the elliptic curve subgroup <``P``>

    - ``m`` - decomposition constant
    
    OUTPUT: optimal factor base size (positive integer)
    
    """    
    return ceil(orderP**(1.0/m))

########################################################################################################
########################################################################################################

def solveECDLP(a, b, orderP):
    """
    Solves the ECDLP from the relations ``a``P + ``b``Q = curve identity.
    
    Finds the integer ``k`` such that ``kP = Q``, if ``b`` is invertible mod ``orderP``.
    
    INPUT:
    
    ``a`` - coefficient of the linear combination associated with ``P``
    
    ``b`` - coefficient of the linear combination associated with ``Q``
    
    ``orderP`` - order of the elliptic curve subgroup <``P``>
    
    OUTPUT:
    
    Solution to the ECDLP, integer ``k`` such that ``kP = Q``.
    
    If ``b`` is not invertible modulo ``orderP``, "None" is returned.
    """
    a = int(a)
    b = int(b)
    res = None
    try:
        res = int(mod(-a*inverse_mod(b, orderP), orderP))
    except:
        pass
    return res

########################################################################################################
########################################################################################################

def buildSumPolySystem(FF, SM3, m, Rx = False):
    """
    Builds a polynomial system consisting of multiple summation polynomials over a finite field ``FF``.
    
    INPUT:
    
    ``FF`` - finite field
    
    ``SM3`` - third summation polynomial for a specific EC
    
    ``m`` - decomposition constant
    
    ``Rx`` - True if we wanna build a polynomial system for a specific point ``R``, used in algorithm 1.
     False otherwise, used in algorithm 2.
     
    OUTPUT:
    
    Returns a vectors polynomials over finite field ``FF`` (generators of an ideal ``I``), 
    vector of formal variables ``x_i`` of length ``m``, vector of bounding variables ``u_i`` of 
    length ``m``-2 for algorithm 1, or length ``m``-3 for algorithm 2, and polynomial ring ``FF[x_1,...,x_m,u_1,...]``.
    
    WARNING: Last summation polynomial has to be added to the ``generators`` manually.
    """
    
    #number of bounding variables 'U'
    numBoundVars = m - 3
    if Rx == True: #last summation polynomial will be S_3(x_m, u_(m-2), Rx)
        numBoundVars += 1
    SMPR = PolynomialRing(FF, 'x', m + numBoundVars, order='degrevlex')
    
    #X-variables
    variablesX = SMPR.objgens()[1][0:m]
    #bounding variables
    variablesU = SMPR.objgens()[1][m:]
    
    generators = [] 
    for k in range(0, numBoundVars):
        if k != 0:
            generators.append(SM3(variablesU[k - 1], variablesU[k], variablesX[k + 1]))
        else:
            generators.append(SM3(variablesX[0], variablesX[1], variablesU[0]))        
    
    #Hotfix: in case when we don't need a bounding variable <=> only 1 summation polynomial will be used.
    #And is added manually.
    if len(variablesU) == 0:
        variablesU = [variablesX[0]]
    return generators, variablesX, variablesU, SMPR

########################################################################################################
########################################################################################################

def buildFactorBaseOnlyX(Q, P, m):
    """

    Builds a factor base (each point has a known decomposition as a linear combination of points  ``P`` and ``Q``, 
    storing only x-coordinates. Used for algorithm 2.
    
    INPUT: 
    
    ``Q`` - another point in a subgroup generated by the point ``P``
    
    ``P`` - base point ``P``
    
    ``m`` - decomposition constant
    
    OUTPUT:
    
    Returns a vector of coordinates ``(a_i, b_i)``, factorbase ``F`` consisting of ``x``-coordinates of points.
    
    Following equality holds: ``a_iP + b_iQ =(x_i,y_i)``, ``x_i`` is in factorbase.
    
    If the solution ``res`` to the ECDLP is found, it's returned as well, otherwise last returned value is ``None``. 
    
    """
    import random
    orderP = P.order()

    factorBaseSize = calcFactorBaseSize(orderP, m)
    factorBase = {} #dict x-coord, index in coord
    coord = []
    
    res = None
    currentSize = 0
    ident = 0*P
    while currentSize < factorBaseSize:
        a = int(random.random() * orderP) #a,b in [0, orderE - 1]
        b = int(random.random() * orderP)
        candidate=(a*P + b*Q)
        candX = candidate[0] #store only x-coordinates
        if candidate == ident and b != 0: #we can solve the ECDLP
            res = solveECDLP(a, b, orderP)
            if res != None:
                break
        elif candX not in factorBase:
            factorBase[candX] = currentSize #store id to the ``coord`` list
            coord.append((a,b))
            currentSize += 1
        else: #there exists an relation aP + bQ = +-(cP + dQ)
            c,d = coord[factorBase[candX]]

            if (c*P + d*Q) != candidate:
                c = -c
                d = -d
            res = solveECDLP(a-c, b-d, orderP)
            if res != None:
                break
            
    return coord, factorBase, res

########################################################################################################
########################################################################################################

def buildFactorBase(Q, P, m):
    """

    Builds a factor base (each point has a known decomposition as a linear combination of points  ``P`` and ``Q``, 
    storing points. Used for algorithm 3.
    
    INPUT: 
    
    ``Q`` - another point in a subgroup generated by the point ``P``
    
    ``P`` - base point ``P``
    
    ``m`` - decomposition constant
    
    OUTPUT:
    
    Returns a vector of coordinates ``(a_i, b_i)``, factorbase ``F`` consisting of points
    ``a_iP + b_iQ =R_i``.
    
    If the solution ``res`` to the ECDLP is found, it's returned as well, otherwise last returned value is ``None``.
    
    """
    import random
    orderP = P.order()

    factorBaseSize = calcFactorBaseSize(orderP, m)
    factorBase = [] #store points
    coord = []
    
    res = None
    currentSize = 0
    ident = 0*P
    while currentSize < factorBaseSize:
        a = int(random.random() * orderP) #a,b in [0, orderE - 1]
        b = int(random.random() * orderP)
        candidate=(a*P + b*Q)
        if candidate == ident and b != 0: #we can solve the ECDLP
            res = solveECDLP(a, b, orderP)
            if res != None:
                break
        elif candidate not in factorBase:
            factorBase.append(candidate)
            coord.append((a,b))
            currentSize += 1
        else: #there exists an relation aP + bQ = cP + dQ
            c,d = coord[factorBase.index(candidate)]

            res = solveECDLP(a-c, b-d, orderP)
            if res != None:
                break
            
    return coord, factorBase, res

########################################################################################################
########################################################################################################

def generateRandomEC(bits = 0, p = 0, primeOrder=False):
    """
    Generates a random elliptic curve defined by the short
    Weierstrass equation over a prime order field.

    INPUT:
    
    - ``bits`` - number of bits of the order (characteristic) of the underlying field
    
    - ``p`` - characteristic of the prime field, if set - must be a positive prime integer

    - ``primeOrder`` - whether we care about the order of the 
                       elliptic curve to be prime
    
    Parameter ``p`` is preferred if set to ``bits``.
    
    We first construct a finite field ``FF`` of prime order with specified
    bit security. ``log[2, #FF]`` =~ ``bits``. Then generate random
    coefficients ``a_4`` and ``a_6`` of the generated elliptic curve.
    We check whether it's a non-singular curve. 
    
    In Sage this elliptic curve can be constructed this way 
    (using the long Weierstrass equation):

    E = EllipticCurve(FF, [0,0,0,a_4,a_6])
    
    OUTPUT: Returns the generated elliptic curve.
    
    EllipticCurve(FF, [0,0,0,a_4,a_6]), where ``a_4`` and ``a_6``
    are random integers. If we require the elliptic curve of
    prime order, we repeat the generation until we one is found,
    if there isn't a prime order EC found, we return an EC
    with the biggest prime factor found.

    EXAMPLES::
    
    b = 11 
    
    E = generateRandomEC(bits=b, primeOrder=True)
    
    print(E) 
    
    print("Order of E is: {}.".format(E.order())) 
    
    sage: Elliptic Curve defined by y^2 = x^3 + 854*x + 303 over Finite Field of size 2053 
    
    sage: Order of E is: 2029.
    
    E = generateRandomEC(p=6421, primeOrder=True)
    
    print(E)
    
    sage: Elliptic Curve defined by y^2 = x^3 + 252*x + 5611 over Finite Field of size 6421
    """
    if (p == 0):
        p = next_prime(int(2**bits));
        
    T = GF(p)
    
    coefs = [0, 0, 0, None, None]
    while True:
        #random a_4
        coefs[3] = T.random_element();
        #random a_6
        coefs[4] = T.random_element();
        try:
            E = EllipticCurve(T, coefs)
            if primeOrder == False or is_prime(E.order()):
                break
        except ArithmeticError: #if E singular we try again
            pass
    return E

########################################################################################################
########################################################################################################

def initECDLP(E):
    """
    Initializes an elliptic curve discrete logarithm
    problem on the selected elliptic curve  ``E``.

    INPUT:

    - ``E`` - ellitic curve on which the problem will be initialized
    
    ECDLP in ``E`` with a generator ``P``, and some other point ``Q``
    is to find an integer ``k`` such that ``kP`` = ``Q``.

    OUTPUT: Returns the generator ``P`` of ``E`` and a random
    point ``Q`` on ``E``. ``Q`` is guaranteed
    to be different to the elliptic curve's ``E`` identity element.

    EXAMPLES::
    
    E = EllipticCurve(GF(17), [0,0,0,1,2])
    
    P, Q = initECDLP(E)
    
    print(P,Q)
    
    sage: Order of P is 24.
    
    sage: ((13 : 11 : 1), (0 : 6 : 1))
    """
    
    import random
    
    P=E.gen(0)
    orderP=P.order()
    #k in [1, orderP-1] => Q != E(0)
    k=int(1+(orderP-1)*random.random())
    Q=k*P
    return P, Q

########################################################################################################
########################################################################################################

def boundVariablesToBase(FF, generators, variablesX, factorBase, m):
    """
    Bounds variables to the provided factorbase by adding additional polynomials to the set of ``generators``.
    
    INPUT: 
    
    ``FF`` - finite field over which the elliptic curve is defined
    
    ``generators`` - generators of the ideal ``I``
    
    ``variablesX`` - vector of formal variables ``X``, which are to be bound to the ``factorBase``
    
    ``factorBase`` - factor base to which are the ``variablesX`` to be bound
    
    ``m`` - decomposition constant, if we want to split the factorbase provide ``m`` = length(``factorBasee``),
    used for algorithm 2, in the opposite case provide ``m`` = 1, used in algorithm 1.
    
    OUTPUT:
    
    Returns modified vector ``generators`` with added bounding polynomials.
    
    """
    FBR.<X> = PolynomialRing(FF, 1, order='degrevlex')
    baseBound = [FBR(1) for k in range(m)]
    
    #divide factorBase into m sets and create m-bounding polynomials
    for elem, k in factorBase.iteritems():
        baseBound[mod(k, m)] *= FBR(X - elem) #add to the m-th base  
    
    if m == len(variablesX):
        for k in range(0,m):
            generators.append(baseBound[k](variablesX[k]))
    elif m == 1:
        for k in range(0,len(variablesX)):
            generators.append(baseBound[0](variablesX[k]))

    return generators

########################################################################################################
########################################################################################################
#                                 Algorithm 1 (inspired by Semaev 2015)                                #
########################################################################################################
########################################################################################################

def algorithm1Semaev(Q, P, m):
    import random
    import time
    
    startTime = time.time()
    nthreads = getNumThreads()
    
    if m < 2:
        raise ValueError("Parameter 'm' has to be at least 2.")
    
    #Elliptic curve
    E = P.curve()
    
    #finite (prime) field
    FF = E.base_field()
    FFmid = float(FF.order())/2.0;
    
    #order of <P>, assuming E = <P>
    orderP = P.order() 
        
    #factorBase size
    fbs = calcFactorBaseSize(orderP, m)
    
    #3rd Semaev summation polynomial for 'E'
    SM3 = construct3rdSumPoly(E) 
    
    #relation matrix field - orderP is prime
    CF = GF(orderP); 

    #max rank is fbs + 1, use Sparse matrix for effective computation
    relationMatrix = matrix(CF, nrows=fbs+1, ncols=fbs+2, sparse=True); 
    
    #build a summation polynomial system to stand-in for m-th summation polynomial
    generators, variablesX, variablesU, SMPR = buildSumPolySystem(FF, SM3, m, Rx = True)

    columnID = 0 
    factorBase = {}
    while columnID < fbs:
        # generate a random x-coordinate
        candX = int(1 + random.random()*(FF.order() - 1)) 
        if candX not in factorBase.keys() and E.is_x_coord(candX):
            factorBase[candX] = columnID
            columnID += 1

    #restrict results to the factor base
    generators = boundVariablesToBase(FF, generators, variablesX, factorBase, 1)

    #we will replace this with SM3(u_{m-2}, x_m, R_x)
    generators.append(None) 
    
    ident = E(0);
    numRel = 0; #number of relations

    isItEnough = False;
    res = None
    totalRel = 0
    gbComputed = 0
    solTm = 0
    
    while isItEnough == False:
        a=int(orderP * random.random())
        b=int(orderP * random.random())
        R = a*P + b*Q
        if R == ident:
            res = solveECDLP(a, b, orderP)
            if res != None:
                break
            else:
                continue

        
        Rx = R[0];
        sT = time.time()
        generators[-1] = SM3(variablesU[-1], variablesX[-1], Rx); 
        tmp = SMPR.ideal(generators) 

       # gb = tmp.groebner_basis('libsingular:slimgb') #good
        gb = Ideal(tmp.groebner_basis('giac:gbasis', prot=False, threads=nthreads)) 

        gbComputed += 1
        #FGLM is not needed, number of relations/solutions to the polynomial system is usually going to be 1, tops 2
#       gb = Ideal(gb.transformed_basis('fglm',LEXSMPR))
    
 #       import fgb_sage
        #Faugere implementation - for prime fields < 2^16
#        gb = Ideal(fgb_sage.groebner_basis(tmp))  #68s / 107s - 37 rel: 15.9 bits of security
        
        solutions = gb.variety()
        solTm += time.time() - sT
        
        addedRel = 0
        for solution in solutions:
            candidates = [E.lift_x(solution[variablesX[k]]) for k in range(m)]
            points = [candidates[k] if float(candidates[k][1]) < FFmid else -candidates[k] for k in range(m)]
            
            for v in VectorSpace(GF(2), m):
                if (R + sum(-points[k] if v[k] else points[k] for k in range(m))) == ident:
                    for k in range(m): 
                        relationMatrix[numRel, factorBase[points[k][0]]] += (-1)**(v[k])
                        
                    relationMatrix[numRel, fbs] = a
                    relationMatrix[numRel, fbs + 1] = b
                    numRel += 1
                    addedRel += 1
                    break
            if numRel >= fbs:
                if fbs not in relationMatrix.pivots(): #cant solve with those relations
                    relationMatrix = copy(relationMatrix.echelon_form()); #make mutable again
                    numRel = relationMatrix.rank()
                #    print("Acquired relations aren't sufficient to solve the ECDLP. Relation matrix rank: {}"\
                 #         .format(numRel))
                  #  sys.stdout.flush()
                else:
                    break
        if addedRel > 0:
            if fbs in relationMatrix.pivots(): #we can solve the ECDLP now
                isItEnough = True
            else:
           #     print("Added {} relations to the relation matrix.".format(addedRel))
                totalRel += addedRel
                      
    if res == None: 
        relationMatrix = relationMatrix.echelon_form();
        ##in the echelon form, so the last nonzero row has to be (0 ... 0 1 c) = > P + cQ = curve identity
        res = solveECDLP(1, relationMatrix[relationMatrix.rank() - 1, fbs + 1], orderP) #0-indexed
    
    totalTime = time.time() - startTime
    if (res*P != Q):
        raise ValueError("Unexpected error: incorrect result.")    

    #print statistics
    printResults(E, P, Q, res, orderP, m, fbs, gbComputed, totalTime, solTm)
    return res, totalRel, totalTime, gbComputed, solTm
    

########################################################################################################
########################################################################################################
#                                  Algorithm 2 (inspired by Amadori 2017)                              #
########################################################################################################
########################################################################################################
def algorithm2Amadori(Q, P, m, t0=3):
    import time
    from sage.libs.giac import groebner_basis as gb_giac

    startTime = time.time()
    nthreads = getNumThreads()
    
    if m < 3:
        raise ValueError("Parameter 'm' has to be at least 3.")
    
    #Elliptic curve
    E = P.curve()
    
    #Elliptic curve identity
    ident = E(0);
    
    orderP = P.order()
    
    #base (prime) field
    FF = E.base_field()
    
    #3rd Semaev summation polynomial for this curve
    SM3 = construct3rdSumPoly(E)
        
    #precompute
    gXUS = []
    for t in range(t0,m+1):
            generators, variablesX, variablesU, SMPR = buildSumPolySystem(FF, SM3, t, Rx = False)
            generators.append(SM3(variablesX[-2], variablesX[-1], variablesU[-1]))
            #save
            gXUS.append((generators,variablesX,variablesU, SMPR))
    
    it = 0
    sumSol = 0
    res = None
    while res == None: #not solved
        
        coord, factorBase, res = buildFactorBaseOnlyX(Q, P, m)
        if res != None:
            break
        
        for t in range(t0, m + 1):
            generators, variablesX, variablesU, SMPR = gXUS[t-t0]
            generators = generators[:m-2]
            generators = boundVariablesToBase(FF, generators, variablesX, factorBase, t)
            
            tSol = time.time()
            tmp = SMPR.ideal(generators) 

            #    gb = Ideal(tmp.groebner_basis('libsingular:slimgb')) #good
            
           # gb = Ideal(tmp.groebner_basis('giac:gbasis', prot=False,threads=4)) 
            gb = gb_giac(tmp, prot=False, threads=nthreads)
            
        #FGLM is not needed, number of relations/solutions to the polynomial system is usually going to be 1, tops 2
         #   gb = Ideal(gb.transformed_basis('fglm',LEXSMPR))
    
     #       import fgb_sage
            #Faugere implementation - for prime fields < 2^16
    #        gb = fgb_sage.groebner_basis(tmp)  
            solutions = Ideal(gb).variety()
            sumSol += time.time() - tSol
            
            for solution in solutions:
                points = [E.lift_x(solution[variablesX[k]]) for k in range(t)]
            
                for v in VectorSpace(GF(2), t):
                    if sum(-points[k] if v[k] else points[k] for k in range(t)) == ident:
                        sumA = 0
                        sumB = 0

                        for k in range(t):
                            baseID = factorBase[points[k][0]]
                            sgn = -1 if v[k] else 1

                            if (coord[baseID][0]*P + coord[baseID][1]*Q) == (sgn*points[k]):
                                sumA += coord[baseID][0]
                                sumB += coord[baseID][1]
                            else: 
                                sumA -= coord[baseID][0]
                                sumB -= coord[baseID][1]
                        res = solveECDLP(sumA, sumB, orderP)
                        if res != None:
                            break

                if res != None:
                    break
                                    
            if res != None:
                break

        it += 1
    totalTime = time.time() - startTime
    if (res*P != Q):
        raise ValueError("Unexpected error: incorrect result.")    
    
    #print statistics
    printResults(E, P, Q, res, orderP, m, len(factorBase), it, totalTime, sumSol)
    return res, it, totalTime, sumSol

    
########################################################################################################
########################################################################################################
#                                   Algorithm 3 (based on McGuire 2017)                                #
########################################################################################################
########################################################################################################

#Multi-index class, dimension is dim
#[i_1, i_2, ..., i_dim]
class MultiIndex:
    def __init__(self, dim, baseSize):
        self.dim = dim
        self.baseSize = baseSize
        self.index = [0 for i in srange(0, self.dim)]
        
    def dbgPrint(self):
        print("Dim: {}, baseSize: {}, index: {}.".format(self.dim, self.baseSize, self.index))

    def getIndex(self):
        return self.index
    
    #returns a multi-index, -1 means the index is out of bounds
    def nextIndex(self):
        isDone = True
        for i in srange(self.dim - 1, -1, -1):
            if (self.index[i] + 1) < self.baseSize:
                isDone = False
                break
        if isDone == True:
            return [-1]
        
        self.index[i] += 1
        for k in srange(i + 1, self.dim):
            self.index[k] = self.index[i]
        return self.index
    
def algorithm3McGuire(Q, P, m):
    import time
    
    startTime = time.time()
    if m < 2:
        raise ValueError("Parameter 'm' has to be at least 2.")
    
    indexDim = m - 1
    
    #Elliptic curve
    E = P.curve()
    
    orderP = P.order()
    
    res = None

    attempts = 0
    fbs = 0
    pointsTried = 0
    while res == None:
        coord, factorBase, res = buildFactorBase(Q, P, m)
        if res != None:
            break

        fbs = len(factorBase)

        multiIndex = MultiIndex(indexDim, fbs)
        index = multiIndex.getIndex()

        while res == None and index[0] != -1:
            
            points = [factorBase[i] for i in index]
            
            for v in VectorSpace(GF(2), indexDim):
                tmp = sum(-points[k] if v[k] else points[k] for k in srange(indexDim))

                if tmp in factorBase:
                    baseId = factorBase.index(tmp)

                    sumB = -coord[baseId][1] + sum(-coord[index[k]][1] if v[k] 
                                              else coord[index[k]][1] for k in srange(0,indexDim))
                    sumA = -coord[baseId][0] + sum(-coord[index[k]][0] if v[k] 
                                              else coord[index[k]][0] for k in srange(0,indexDim))
                    
                    res = solveECDLP(sumA, sumB, orderP)
                    if res != None:
                        break

                pointsTried += 1        
            index = multiIndex.nextIndex()
        attempts += 1  
    totalTime = time.time() - startTime
    
    if (res*P != Q):
        raise ValueError("Unexpected error: incorrect result.")    

    #print statistics
    printResults(E, P, Q, res, orderP, m, fbs, attempts, totalTime, 0)
    
    return res, attempts, totalTime, pointsTried
     
    


#EXAMPLE USAGE:

#generate a random prime order Elliptic Curve ~~ 2**18
E = generateRandomEC(bits=18, primeOrder=True)

#obtain its generator and a random point Q in <P>
P, Q = initECDLP(E)

#run a selected algorithm to solve the ECDLP
result, iterations, totalTime, GBtime = algorithm2Amadori(Q, P, m=5, t0=3)

