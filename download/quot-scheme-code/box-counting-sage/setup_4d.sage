"""
Configuration for rings, variables, cohomology theory.
"""
from sage.rings.fraction_field_element import FractionFieldElement
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.rings.polynomial.laurent_polynomial_ring import is_LaurentPolynomialRing
from sage.rings.power_series_ring import is_PowerSeriesRing
from sage.rings.multi_power_series_ring import is_MPowerSeriesRing
from sage.rings.laurent_series_ring import is_LaurentSeriesRing
from sage.rings.fraction_field import is_FractionField
from sage.structure.element import is_Matrix
from sage.combinat.sf.sfa import is_SymmetricFunction
import itertools

    
    
class Default4d:
    
    KT_vars = ['x1','x2','x3','x4','y','w']
    sqrtKT_vars = ['u1','u2','u3','u4','w','sqrtv']
    coho_vars = ['t1','t2','t3','t4','m','halfm']
    
    KT_ring = LaurentPolynomialRing(QQ, KT_vars)
    sqrtKT_ring = LaurentPolynomialRing(QQ, sqrtKT_vars)
    coho_ring = LaurentPolynomialRing(QQ, coho_vars)
    
    ff = GF(next_prime(10^8))
    series_ring = LaurentPolynomialRing(KT_ring.fraction_field(), 'q')
    sqrtseries_ring = LaurentPolynomialRing(sqrtKT_ring.fraction_field(), 'q')
    cohoseries_ring = LaurentPolynomialRing(coho_ring.fraction_field(), 'q')
    
    x1,x2,x3,x4,y,v = KT_ring.gens()
    u1,u2,u3,u4,w,sqrtv = sqrtKT_ring.gens()
    t1,t2,t3,t4,m,halfm = coho_ring.gens()
    
    
    

class VectorBundle4d:
    
    def character(partition, weight):
        x1,x2,x3,x4,y = [Default4d.KT_ring.gen(i) for i in range(5)]
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        return sum(Q * x1^(weight[3*i]) * x2^(weight[3*i+1]) * x3^(weight[3*i+2]) for i in range(len(weight)/3))
    
class KTheory4d:
    """
    Container for K-theoretic methods
    """
    name = "K-theory" # printed name
    
    @staticmethod
    def from_monomial(m):
        """
        Convert the K-theoretic monomial `m` into a K-theoretic monomial.
        """
        return m
    
    
    @staticmethod
    def NekBracket(f, check=False):
        r"""
        Computes the Nekrasov bracket $[x]=x^{1/2}-x^{-1/2}$ of K-theory class `f`. Output in sqrtKT_ring where $u=x^{1/2}$.
        """
        R = f.parent()
        S = Default4d.sqrtKT_ring

        if R==Default4d.KT_ring: 
            numer, denom = S.one(), S.one()
            for exp, coeff in f.dict().items():
                # create the term x^(1/2) - x^(-1/2)=u-u^(-1)
                if exp.is_constant():
                    term = S.zero()
                else:
                    term = S({exp: 1, exp.emul(-1): -1})
                if coeff > 0:
                    numer *= term ** (coeff)
                elif coeff < 0:
                    denom *= term ** (-coeff)
            return S.fraction_field()(numer) / denom

        else:
            raise NotImplementedError("%s (%s)" % (R, f))
      
    @staticmethod      
    def dual(f, check=False):
        r"""
        Reverses the signs of exponents on `f`.
        """
        R = f.parent()

        if R==Default4d.KT_ring: # use a fast implementation
            g=R.zero()
            for exp, coeff in f.dict().items():
                g+= R({exp.emul(-1): coeff})
            return g

        else:
            raise NotImplementedError("%s (%s)" % (R, f))
            
    def sqrt_to_original(f):
        r"""
        changes all the u^2 to x (can only be done if the powers on u are even).
        """
        R = f.parent()
        S = Default4d.KT_ring

        if R==Default4d.sqrtKT_ring: 
            term=S.zero()
            for exp, coeff in f.dict().items():
                newexp=()
                for i in range(4):
                    newexp+=(exp[i]/2,)
                    
                newexp+=(0,exp[4],)
                term +=S({newexp:coeff})
            return term
            
        else:
            raise NotImplementedError("%s (%s)" % (R, f))
            
    def log_universal_transformation(f,prec):
        
        r"""
        returns exp( \sum_n \sum_{l|n} l^2 f(n) ) to precision.
        """
        
        R = f(1).parent()
        
        
        g = sum( sum(((l+1)^2 if (n+1)%(l+1)==0 else 0) for l in range((n+1)))*f(n+1) for n in range(prec)  )
        return g
    
    def series_exp(f,prec):
        R = f.parent()
        return sum( (f^k/factorial(k) for k in range(prec+1)), R.zero() )
    
    def highest_degree_y(f):
        R = f.parent()
        max_deg=0
        for exp, coeff in f.dict().items():
            if exp[4]>max_deg:
                max_deg = exp[4]
        term=R.zero()
        for exp, coeff in f.dict().items():
            if exp[4]==max_deg:
                term+=R({exp:coeff})
        return term
    
    def lowest_degree_y(f):
        R = f.parent()
        min_deg=0
        for exp, coeff in f.dict().items():
            if exp[4]<min_deg:
                min_deg = exp[4]
        term=R.zero()
        for exp, coeff in f.dict().items():
            if exp[4]==min_deg:
                term+=R({exp:coeff})
        return term
    
    
class Cohomology4d:
    """
    Container for special 4d cohomological methods. K-theory classes are in variables $x_1,...,x_4,y$, 
    cohomological ones are in $t_1,...,t_4,m$.
    """
    name = "cohomology4d" # printed name

    @staticmethod
    def from_monomial(m):
        """
        Convert the K-theoretic monomial `x_1^{i_1}...x_4^{i_4}y^i` into cohomological $i_1t_1+...+i_4t_4+im$. 
        This is taking first chern class.
        """
        R = m.parent()
        if R== Default4d.KT_ring:
            return sum(m.degree(R.gen(i)) * Default4d.coho_ring.gen(i) for i in range(len(Default4d.coho_ring.gens())))
        elif R==Default4d.sqrtKT_ring:
            return sum((1/2)*m.degree(R.gen(i)) * Default4d.coho_ring.gen(i) for i in range(len(Default4d.coho_ring.gens())))
        else:
            raise NotImplementedError("%s" % R)
            
    
    @staticmethod
    def from_character_to_coho(f, prec):
        """
        Convert the K-theoretic monomial `x` into cohomological $1 + t + t^2/2 + t^3/6 + ...$ with precision `prec`. 
        """
        
        if f in ZZ:
            return f
        
        R = f.parent()
        
        
        S = Default4d.coho_ring
        
        def ex(i,exp):
            return 1+sum((exp*S.gen(i))^(k+1)/factorial(k+1) for k in range(prec))
        
        def trunc(P, N):
            r"""
            Return this polynomial truncated to total degree N.
            """
            trunc = {dd: c for dd, c in P.dict().items() if sum(dd) <= N}
            return P.parent()(trunc)

        if R==Default4d.KT_ring: 
            total = S.zero()
            for exp, coeff in f.dict().items():
                term = S.one()
                if exp.is_constant():
                    term = S.one()
                else:
                    for i in range(len(exp)-1):
                        term *= ex(i,exp[i])
                        term = trunc(term, prec)
                    term *= ex(4,exp[5]/2)
                    term = trunc(term, prec)
                term *=coeff
                total+=term
            return total
        elif R==Default4d.sqrtKT_ring:
            total = S.zero()
            for exp, coeff in f.dict().items():
                term = S.one()
                if exp.is_constant():
                    term = S.one()
                else:
                    for i in range(len(exp)):
                        term *= ex(i,exp[i]/2)
                        term = trunc(term, prec)
                term *=coeff
                total+=term
            return total
        else:
            raise NotImplementedError("%s (%s)" % (R, f))

    @staticmethod
    def from_character(f):
        """
        Converts a character ``f`` (from K-theory) to a list of
        cohomological weights in the numerator and denominator.
        Can be used for applying to functors such that $F(V oplus W)=F(V)F(W)$.
        """
            
        numer, denom = [], []

        for coeff, mon in list(f):
            wt = Cohomology4d.from_monomial(mon)
            if coeff > 0:
                numer += (coeff) * [wt]
            elif coeff < 0:
                denom += (-coeff) * [wt]
        return numer, denom
    
        
    
    @staticmethod
    def top_chern(f):
        r"""
        Returns the top chern class of K-theory class ``f``.

        This first converts ``f`` into a list of cohomological weights,
        and then takes the product of all such weights. The result
        always lives in the fraction field of the weight ring.
        """
        numer, denom = Cohomology4d.from_character(f)
        return Default4d.coho_ring.fraction_field()(prod(numer) / prod(denom))
    
    @staticmethod
    def chern_class(k, f):
        r"""
        Computes the `k`-th Chern class of the K-theoretic `f`.
        """
        roots = sum((c*[Cohomology4d.from_monomial(w)] for c, w in f), [])
        return Default4d.coho_ring(sum(prod(S) for S in itertools.combinations(roots, k)))
    
    @staticmethod
    def total_chern(f):
        r"""
        Computes the total Chern class of the K-theoretic `f`.
        """
        numer, denom = Cohomology4d.from_character(f)
        new_numer=[x+1 for x in numer]
        new_denom=[x+1 for x in denom]
        return Default4d.coho_ring.fraction_field()(prod(new_numer+[1]) / (prod(new_denom)))
    
    @staticmethod
    def segre_class(k, f):
        r"""
        Computes the `k`-th Segre class of the K-theoretic `f`.
        """
        def dPart( F, d ):
            return sum( [ F.monomial_coefficient(m) * m for m in F.monomials() if  m.degree() == d ] )
        
        roots = sum((c*[Cohomology4d.from_monomial(w)] for c, w in f), [])
        segre = prod( 1+sum((-1*S)^(K+1) for K in range(k)) for S in roots)
        return dPart(segre,k)
    
    @staticmethod
    def measure_unsymmetrized_coho(f, prec):
        def trunc(P, N):
            r"""
            Return this polynomial truncated to total degree N.
            """
            trunc = {dd: c for dd, c in P.dict().items() if sum(dd) <= N}
            return P.parent()(trunc)
        
        R = Default4d.coho_ring
            
        total = R.one()
        for exp,coeff in f.dict().items():
            coh = sum(exp[i]*Default4d.coho_ring.gens()[i] for i in range(4))
            if coeff < 0:
                total *= sum(coh^k/factorial(k) for k in range(prec+1))-1
            elif coeff > 0:
                total *= sum(coh^k*bernoulli_polynomial(1, k)/factorial(k) for k in range(prec+2))/coh
            if is_FractionField(total.parent()):
                total = trunc(total.numerator(),prec)/total.denominator()
            else:
                total=trunc(total,prec)
            
        
        return total
    
    
def Rational_to_Laurent(f,sqrt=False):
    r"""
    If an element in the fraction field of K-theory has monomial as denominator, 
    this converts it into a Laurent polynomial.
    """
    
    if sqrt:
        R=Default4d.sqrtKT_ring
    else:
        R=Default4d.KT_ring
    
    numer=f.numerator()
    denom=f.denominator()
    expd,coeffd = list(denom.dict().items())[0]
    g=R.zero()
    for exp, coeff in numer.dict().items():
        newexp=()
        for i in range(len(exp)):
            newexp+=(exp[i]-expd[i],)
        g += R({newexp: coeff/coeffd})
    return g
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    

