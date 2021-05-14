from sage.geometry.newton_polygon import NewtonPolygon

def isIsolatedValue(slopes, value):
    inList = False
    for slope in slopes:
        if slope == value:
            if inList:
                return False
            else:
                inList = True
    return inList

def gcdOfList(polys):
    if len(polys) == 0:
        return None
    else:
        output = polys[0]
        for P in polys[1:]:
            output = output.gcd(P)
        return output

#class PolynomialRing: basic parent class for polynomials so some stuff will work
#     def __init__(self):
#         pass

class Polynomial:

    def __init__(self, coefficients):
        if len(coefficients) == 0:
            self.coeffs = [0]
        else:
            self.coeffs = coefficients
        self.degree = 0
        self.indeterminate = "x"
        if type(self.coeffs[0]) == type(self): #if coefficients are polynomials
            self.base = None
        else:
            self.base = self.coeffs[0].parent()
            self.valued = (type(self.base) == type(ValuedField()))
        if self.base:
            if self.valued:
                self.iszero = lambda x : x.iszero()
            else:
                self.iszero = lambda x : x == 0
        else:
            self.iszero = lambda P : P == P.zeroPoly()
        for i in range(len(coefficients)-1,0,-1):
            if not self.iszero(coefficients[i]):
                self.degree = i
                break

    def getCoeffs(self):
        return self.coeffs

    def copy(self):
        return Polynomial(self.coeffs)

    def getDegree(self):
        return self.degree
    
    def leading(self):
        return self.getCoefficient(self.degree)

    def __len__(self): #for iterating over coefficients
        return self.degree+1

    def zero(self):
        if self.base:
            if self.valued:
                return self.base.zero
            else:
                return self.base(0)
        else:
            return self.coeffs[0].zeroPoly()

    def zeroPoly(self):
        return Polynomial([self.zero()])

    def one(self):
        if self.base:
            if self.valued:
                return self.base.one
            else:
                return self.base(1)
        else:
            return self.coeffs[0].onePoly()

    def onePoly(self):
        return Polynomial([self.one()])

    def getCoefficient(self, n):
        if n > self.degree:
            return self.zero()
        else:
            return self.coeffs[n]

    def monomial(self, a, n=0): #returns ax^n
        return Polynomial([self.zero()]*n+[a])

    def evalulate(self, x):
        return sum([self.coeffs[i]*x^i for i in range(self.degree+1)])

    def __add__(self, other):
        newdeg = max(self.degree, other.degree)
        return Polynomial([self.getCoefficient(i)+other.getCoefficient(i) for i in range(newdeg+1)])

    def __mul__(self, other):
        newdeg = self.degree+other.degree
        return Polynomial([sum([self.getCoefficient(j)*other.getCoefficient(i-j) for j in range(i+1)], self.zero()) for i in range(newdeg+1)])
    
    def __pow__(self, n): #repeated multiplication
        if n <= 0:
            return self.onePoly()
        else:
            return self*self**(n-1)

    def __neg__(self):
        return Polynomial([-a for a in self.coeffs])

    def __sub__(self, other):
        return self+-other

    def __mod__(self, other):
        d1, d2 = self.degree, other.getDegree()
        #print(d1,d2)
        if d2 == 0:
            return self.zeroPoly()
        elif d1 < d2:
            return Polynomial(self.coeffs)
        else:
            a = self.coeffs[d1]/other.getCoefficient(d2)
            return (self-other*self.monomial(a,d1-d2))%other

    def __floordiv__(self, other):
        d1, d2 = self.degree, other.degree
        if d2 == 0 and other.iszero(other.coeffs[0]):
            print("divide by 0 error")
            return self.zeroPoly()
        elif d1 < d2:
            return self.zeroPoly()
        elif d1 == d2:
            return Polynomial([self.coeffs[d1]/other.coeffs[d2]])
        else:
            a = self.leading()/other.leading()
            term = self.monomial(a,d1-d2)
            return term + (self-other*term)//other


    def __truediv__(self, other):
        return self//other #may want to implement this separately later
    
    def constDiv(self, num):
        return Polynomial([a/num for a in self.coeffs])

    def __eq__(self, other):
        return self.coeffs == other.getCoeffs()

    def gcd(self, other):
        d1, d2 = self.degree, other.getDegree()
        #print(d1,d2)
        if d1 == 0 and self.iszero(self.coeffs[0]):
            return Polynomial(other.getCoeffs())
        elif d2 == 0 and other.iszero(other.getCoefficient(0)):
            return Polynomial(self.coeffs)
        elif d1 >= d2:
            return other.gcd(self%other)
        else:
            return self.gcd(other%self)

    def gcdLinCombo(self, other): #return (d,P,Q) s.t. self*P+other*Q=d and d = gcd(self,other)
        d1, d2 = self.degree, other.getDegree()
        if d1 == 0 and self.iszero(self.coeffs[0]):
            return (other.copy(), self.zeroPoly(), other.onePoly())
        elif d2 == 0 and other.iszero(other.getCoefficient(0)):
            return (self.copy(), self.onePoly(), other.zeroPoly())
        elif d1 >= d2:
            quotient, remainder = self/other, self%other # self = quotient*other + remainder
            d, P, Q = other.gcdLinCombo(remainder) # P*other + Q*remainder = d, d = gcd(self, other)
            return (d, Q, P-Q*quotient) # d = P*other + Q*(self - quotient*other) = Q*self + (P-Q*quotient)*other
        else:
            quotient, remainder = other/self, other%self # other = quotient*self + remainder
            d, P, Q = self.gcdLinCombo(remainder) # P*self + Q*remainder = d, d = gcd(self, other)
            return (d, P-Q*quotient, Q) # d = P*self + Q*(other - quotient*self) = (P-Q*quotient)*self + Q*other

    def inverseMod(self, generator): #finds inverse mod <generator>, assumes relatively prime for now
        d, P, Q = self.gcdLinCombo(generator)
        return P/d
    
    def cont(self): #content is the gcd of coefficients, this will only work for polynomials over euclidean domain
        return gcdOfList(self.coeffs)
    
    def resultant(self, other): #returns element of self.base. implementing Cohen's algorithm.
        d1, d2 = self.degree, other.degree
        if (d1 == 0 and self.iszero(self.coeffs[0])) or (d2 == 0 and other.iszero(other.coeffs[0])):
            #print("zero")
            return self.zero()
        else:
            s = self.one()
            if d1 >= d2:
                A, B = self, other
            else:
                A, B = other, self
                if A.degree%2 == 1 and B.degree%2 == 1:
                    s = -s
            a, b = A.cont(), B.cont()
            A, B = A.constDiv(a), B.constDiv(b)
            g, h = self.one(), self.one()
            t = a**B.degree * b**A.degree
            while B.degree > 0:
                d1, d2 = A.degree, B.degree
                delta = d1-d2
                if d1%2 == 1 and d2%2 == 1:
                    s = -s
                R = (self.monomial(B.leading()**(delta+1))*A)%B
                A = B
                B = R/self.monomial(g*h**delta)
                g = A.leading()
                h = h**(1-delta)*g**delta
            h = h**(1-d2)*B.leading()**d2
            return s*t*h
    
    def tschirnhaus(self, other, k=0): #returns T_{self,other}. prod(X-other(alpha)) where alpha ranges through roots of self in its splitting field
        #think of A and B as polynomials in Y whose coefficients are polynomials in X (mostly constant polynomials except the Y-constant term of B)
        A = Polynomial([self.monomial(a) for a in self.coeffs])
        x = Polynomial([self.monomial(self.one(),1)])
        yk = Polynomial([self.onePoly()]+[self.zeroPoly()]*k)
        B = Polynomial([self.monomial(a) for a in other.coeffs])
        return A.resultant(x-yk*B)

    def __str__(self): #this can be improved a lot
        output = ""
        for i in range(self.degree+1):
            output += str(self.coeffs[i])+str(self.indeterminate)+"^"+str(i)+" + "
        return "("+output+")"

class ValuedField:

    #default values (for Q)
    ZERO = 0
    ONE = 1
    MINUSONE = -1
    def ADDITION(x,y):
        return x+y
    def MULTIPLICATION(x,y):
        return x*y
    def INVERSE(x):
        return 1/x
    def ISZERO(x):
        return x == 0
    def INRING(x):
        return FALSE
    def INIDEAL(x):
        return FALSE
    #maybe last two should be different

    def __init__(self, zero=ZERO, one=ONE, minusone=MINUSONE, addition=ADDITION, multiplication=MULTIPLICATION, inverse=INVERSE, iszero=ISZERO, inring=INRING, inideal=INIDEAL, valuation=None):
        self.zero, self.one, self.minusone = self(zero), self(one), self(minusone)
        self.addition, self.multiplication, self.inverse = addition, multiplication, inverse
        self.iszero, self.inring, self.inideal = iszero, inring, inideal
        self.valuation = valuation
        self.subtraction = lambda x, y : addition(x, multiplication(minusone, y))
        self.division = lambda x, y : multiplication(x, inverse(y))

    def zero(self):
        return self.FieldElement(self.zero, self)

    def one(self):
        return self.FieldElement(self.one, self)

    def minusone(self):
        return self.FieldElement(self.minusone, self)

    def constructElement(self, num):
        return self.FieldElement(num, self)
    
    def __call__(self, num):
        return self.constructElement(num)

    def addition(self):
        return self.addition

    def multiplication(self):
        return self.multiplication

    def inverse(self):
        return self.inverse

    def iszero(self):
        return self.iszero

    def inring(self):
        return self.inring

    def inideal(self):
        return self.inideal

    def valuation(self):
        return self.valuation

    def subtraction(self):
        return self.subtraction

    def division(self):
        return self.division

    def makeNP(self, P):
        return NewtonPolygon([(i, P.getCoefficient(-i-1).val()) for i in range(len(P))])

    def isNewtonPair(self, P, value):
        return isIsolatedValue(self.makeNP(P).slopes(), value)
    
    def presentation(self, P, value): #returns immediate presentation of the root of P with valuation value, assumes P, value is a newton pair
        n = P.degree
        L = self.makeNP(P).slopes()
        i = L.index(value) #v(a_{n-i-1})-v(a_{n-i})
        return -P.getCoefficient(n-i-1)/P.getCoefficient(n-i)

    class FieldElement:

        def __init__(self, num, field):
            self.num = num
            self.field = field

        def parent(self):
            return self.field

        def __add__(self, other):
            return self.field(self.field.addition(self.num, other.num))

        def __sub__(self, other):
            return self.field(self.field.subtraction(self.num, other.num))

        def __mul__(self, other):
            return self.field(self.field.multiplication(self.num, other.num))
        
        def __pow__(self, n):
            if n <= 0:
                return self.field.one
            else:
                return self*self**(n-1)

        def __truediv__(self, other):
            return self.field(self.field.division(self.num, other.num))

        def __neg__(self):
            return self*self.field.minusone

        def __eq__(self, other):
            return self.field.iszero(self.field.subtraction(self.num, other.num))

        def __ne__(self, other):
            return not self==other
        
        def iszero(self):
            return self.field.iszero(self.num)

        def val(self):
            return self.field.valuation(self.num)
        
        def __str__(self):
            return str(self.num)

    class NewtonExtensionElement:

        def __init__(self, P, value, Q): #represents coset I_{P,value}+Q
            self.P = P #a Polynomial
            self.value = value
            self.Q = Q%P #a Polynomial. we can simplify by just using Q mod P

        def getP(self):
            return self.P

        def getValue(self):
            return self.value

        def getNewtonPair(self):
            return (self.P, self.value)

        def getQ(self):
            return self.Q
    
    def constructNewtonExtensionElement(self, P, value, Q):
        return NewtonExtensionElement(P, value, Q)

    def constructNewtonExtension(self, P, value):
        if not self.isNewtonPair(P, value):
            return self

        def addition(p,q):
            if p.getNewtonPair() != q.getNewtonPair():
                print("elements from different extensions")
                return None
            else:
                return NewtonExtensionElement(p.getP(), p.getValue(), p.getQ()+q.getQ())

        def multiplication(p,q):
            if p.getNewtonPair() != q.getNewtonPair():
                print("Elements from different extensions")
                return None
            else:
                return NewtonExtensionElement(p.getP(), p.getValue(), p.getQ()*q.getQ())

        def iszero(p): #p.Q is in I_{P,value} <=> gcd(p.Q,P.Q) has slope of value
            divisor = p.getQ().gcd(P)
            return value in self.makeNP(divisor).slopes()

        def inverse(p):
            if iszero(p):
                print(str(p.getQ())+" is not invertible")
                return None
            else:
                generator = p.Q/p.Q.gcd(P) #this is the P_0 in the last paragraph of lemma 5.5
                return p.Q.inverseMod(generator)
            
        z = self.presentation(P, value) #immediate presentation of the adjoined root
        
        def immPresentation(p): #should return a FieldElement of the base field (self)
            if p.Q.degree == 0:
                return self.constructElement(p.Q.getCoefficient(0))
            #elif p.Q == p.Q.monomial(p.Q.one(),1): #if p represents the adjoined root
            L = self.makeNP(P).slopes()
            L0 = self.makeNP(P.tschirnhaus(p.Q)).slopes()
            k = 0 # first find k as described in lemma 5.6
            foundk = False
            while not foundk:
                kworks = True
                for gamma in L:
                    if gamma != value:
                        for delta1 in L0:
                            for delta2 in L0:
                                if k*(gamma-value) == delta1-delta2:
                                    kworks = False
                                    break
                            if not kworks:
                                break
                        if not kworks:
                            break
                if kworks:
                    foundk = True
                else:
                    k += 1
            Tk = P.tschirnhaus(p.Q, k)
            Lk = self.makeNP(Tk).slopes()
            for delta in Lk:
                if delta - k*value in L0:
                    break
            z1 = self.presentation(Tk, delta) #immediate presentation of the isolated root of Tk that we want
            return z1/(z**k)
        
        def valuation(p):
            return immPresentation(p).val()
        
        def inring(p):
            return valuation(p) >= 0
        
        def inideal(p):
            return valuation(p) > 0
                    
        def baseToPoly(num):
            return self.constructNewtonExtensionElement(P, value, Polynomial([num]))

        return ValuedField(baseToPoly(self.zero), baseToPoly(self.one), baseToPoly(self.minusone), addition, multiplication, inverse, iszero, inring, inideal, valuation)

def ValuedQQ(valuation):
    def inring(x):
        return valuation(x) >= 0
    def inideal(x):
        return valuation(x) > 0
    return ValuedField(inring=inring,inideal=inideal,valuation=valuation)

def fieldPoly(field, coeffs):
    return Polynomial([field(a) for a in coeffs])

#v = QQ.valuation(2)
#Q2 = ValuedQQ(v)
#P = fieldPoly(Q2, [2,1,1])
#K = Q2.constructNewtonExtension(P,0)
q = Polynomial([5,0,1])
p = Polynomial([2,0,1])
#r = Polynomial([0,1,1])
#s = Polynomial([0])
#t = Polynomial([r,q])
#u = Polynomial([r,s])
#print(t.getCoefficient(1)*u.getCoefficient(2))
print(p.tschirnhaus(q))