"""
Pointlike DT vertices on CC^4 (no edges, legs).
"""
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from itertools import chain, combinations

load("setup.sage")
load("setup_4d.sage")

load("partition_3d.sage")
load("partition_4d.sage")


pP4ds = Partitions4d()
x1,x2,x3,x4,y,v=Default4d.KT_ring.gens()
u1,u2,u3,u4,w,sqrtv = Default4d.sqrtKT_ring.gens()
t1,t2,t3,t4,m,halfm = Default4d.coho_ring.gens()
q=Default4d.cohoseries_ring.gen()
b=var('b')
w1,w2,w3=var('w1'),var('w2'),var('w3')
w4,w5,w6=var('w4'),var('w5'),var('w6')

class Vertex4d(UniqueRepresentation):
    
    
    r"""
    Pointlike DT vertices on $\CC^4$
    """
    @staticmethod
    def __classcall_private__(cls, ct=KTheory):
        # UniqueRepresentation objects cannot have mutable parameters.
        # So we need to make lamb, mu, nu into Partitions.
        return cls.__classcall__(cls, ct)

    def __init__(self, ct):
        self._partitions = Partitions4d()
        self._ct = ct

    def __repr__(self):
        return "4d vertex with no legs"

    @staticmethod
    def Tvir(partition, x1=Default4d.x1,x2=Default4d.x2,x3=Default4d.x3,x4=Default4d.x4, specialize=False):
        r"""
        Computes the (K-theoretic) weight of virtual tangent space.

        This is the function `V_{\alpha}` in MNOP I (Cao-Kool for 4d).
        """
        if specialize:
            x4=1/x1*1/x2*1/x3

        Q = partition.character(x1, x2, x3, x4)

        Q_inv = partition.character(x1^-1, x2^-1, x3^-1, x4^-1)

        # T = Q + \bar{Q}/x_1x_2x_3x_4 - Q \bar{Q} (1-x_1)(1-x_2)(1-x_3)(1-x_4) / x_1x_2x_3x_4
        T = Q + Q_inv/(x1*x2*x3*x4) - Q * Q_inv * (1-x1)*(1-x2)*(1-x3)*(1-x4)/(x1*x2*x3*x4)
            
        return Default4d.KT_ring(T)
    
    def sqrtTvir(partition,x1=Default4d.x1,x2=Default4d.x2,x3=Default4d.x3,check=False):
        r"""
        Computes the (K-theoretic) square root of virtual tangent space.
        """
        
        
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        
        Q_inv = partition.character(x1^-1, x2^-1, x3^-1, x4=x1*x2*x3)
        
        sqrtT = Q-(1-1/x1)*(1-1/x2)*(1-1/x3)*Q*Q_inv
        
        if check:
            sqrtT_inv = Vertex4d.sqrtTvir(partition,x1^-1, x2^-1, x3^-1,False)
            if sqrtT+sqrtT_inv!=Vertex4d.Tvir(partition, specialize=true):
                raise ValueError("something went wrong in computation"+partition.__str__())
        
        return sqrtT
    
    
        

    @cached_method
    def _term(self, k, descendant=None):
        r"""
        Returns the degree $k$ term of $\sum_{\pi} \frac{(-q)^{|\pi|} f(\pi)}{e(T_\pi^{vir})}$
        for some function $f$ indicated by `descendant`.
        """
        R = Default.boxcounting_ring.base_ring()
        x, y, z = Default.x, Default.y, Default.z
        if descendant is None:
            descendant = lambda f: R.one()

        return sum(R(self._ct.measure(self.__class__.weight(PP))) *
                   R(descendant(PP._unnormalized_character(x,y,z)))
                   for PP in self._partitions.with_num_boxes(k))

    def term(self, k, x=Default.x, y=Default.y, z=Default.z, descendant=None):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``, in variables `x, y, z`.
        """
        res = self._term(k, descendant)
        if (x, y, z) != (Default.x, Default.y, Default.z):
            res = res.subs(x=x, y=y, z=z)
        return res

    @cached_method
    def series_unreduced(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q, descendant=None):
        r"""
        Return the *unreduced* series corresponding to ``self``,
        indexed by `-q`. The series will have precision ``prec``,
        i.e. will contain exactly ``prec`` terms.
        """
        min_vol = self._partitions.minimal_volume()
        if prec <= 0:
            return q.parent().zero().add_bigoh(min_vol)

        res = sum(self.term(k, x,y,z, descendant) * (-q)^(k+min_vol)
                  for k in range(prec))
        return res.add_bigoh((prec + min_vol)*q.valuation())

    @cached_method
    def series(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q, descendant=None):
        r"""
        Return the series corresponding to ``self``, indexed by `-q`.
        The series will have precision ``prec``, i.e. will contain
        exactly ``prec`` terms.
        """
        res = self.series_unreduced(prec, x,y,z, q, descendant)
        if prec <= 0:
            return res # no need to normalize by "zero"
        else:
            deg0 = self.__class__([], [], [], ct=self._ct)
            return res / deg0.series_unreduced(prec, x,y,z, q)
        
    def Nek(weight,n):
        return sum( SP.sign()*\
        KTheory4d.NekBracket(KTheory4d.dual(VectorBundle4d.character(SP, weight)*Default4d.y^(-1)))\
        *KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP)) for SP in list(pP4ds.with_num_boxes(n)))

    
    def Verlinde(weight,n):
        return sum( SP.sign()*\
                KTheory.measure_unsymmetrized(Vertex4d.sqrtTvir(SP))*\
                   #(Default4d.u1^2,Default4d.u2^2,Default4d.u3^2,Default4d.u4^2,Default4d.w^2,Default4d.sqrtv^2)*\
                #KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP))*\
                   #twist:
                #Default4d.KT_ring(KTheory.determinant(VectorBundle4d.character(SP, (0,0,0))))(Default4d.u1,Default4d.u2,Default4d.u3,Default4d.u4,Default4d.w,Default4d.sqrtv)*\
                KTheory.determinant(VectorBundle4d.character(SP, weight))\
                   #(Default4d.u1^2,Default4d.u2^2,Default4d.u3^2,Default4d.u4^2,Default4d.w^2,Default4d.sqrtv^2)\
                   for SP in list(pP4ds.with_num_boxes(n)))
    
    def Verlinde_no_twist(weight,n):
        return sum( SP.sign()*\
                KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP))*\
                Default4d.KT_ring(KTheory.determinant(-VectorBundle4d.character(SP, weight)))\
                   (Default4d.u1^2,Default4d.u2^2,Default4d.u3^2,Default4d.u4^2,Default4d.w^2,Default4d.sqrtv^2)\
                   for SP in list(pP4ds.with_num_boxes(n)))
    
    def Verlinde_with_sign(weight,n,sign):
        total=0
        for i in range(len(list(pP4ds.with_num_boxes(n)))):
            SP=list(pP4ds.with_num_boxes(n))[i]
            total+=sign[i]*KTheory.measure_unsymmetrized(Vertex4d.sqrtTvir(SP))*\
                    Default4d.KT_ring(KTheory.determinant(VectorBundle4d.character(SP, weight)))
        return total
    
    
    
    def Verlinde2(weight,n):
        return sum( SP.sign()*\
                KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP))*\
                Default4d.KT_ring(KTheory.determinant(-VectorBundle4d.character(SP, weight)))\
                   (Default4d.u1,Default4d.u2,Default4d.u3,Default4d.u4,Default4d.w,Default4d.sqrtv)\
                   for SP in list(pP4ds.with_num_boxes(n)))

    def sqrtVerlinde(weight,n):
        r = len(weight)/3
        DetWeight = ( sum(weight[i*3] for i in range(r)),sum(weight[i*3+1] for i in range(r)),sum(weight[i*3+2] for i in range(r)))
        return sum(SP.sign()*
               KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP))*
               Default4d.KT_ring(KTheory.determinant(VectorBundle4d.character(SP, DetWeight)))
                   (Default4d.u1,Default4d.u2,Default4d.u3,Default4d.u4,Default4d.w,Default4d.sqrtv)*
               Default4d.KT_ring(KTheory.determinant(VectorBundle4d.character(SP, (0,0,0))))
                   (Default4d.u1^2,Default4d.u2^2,Default4d.u3^2,Default4d.u4^2,Default4d.w^2,Default4d.sqrtv^2)^r
               for SP in list(pP4ds.with_num_boxes(n)))

    
    def Nek_with_det(weight,n):
        r=len(weight)/3
        DetWeight = ( sum(weight[i*3] for i in range(r)),sum(weight[i*3+1] for i in range(r)),sum(weight[i*3+2] for i in range(r)))
        return sum( SP.sign()*\
        KTheory4d.NekBracket(KTheory4d.dual(VectorBundle4d.character(SP, DetWeight)*Default4d.y^(-1)))*\
        KTheory4d.NekBracket(KTheory4d.dual(KTheory.determinant(VectorBundle4d.character(SP, (0,0,0)))*Default4d.y^(-1)))^(2*Integer(r))*\
        KTheory4d.NekBracket(-Vertex4d.sqrtTvir(SP)) for SP in list(pP4ds.with_num_boxes(n)))
    
    
    def Total_Chern(weight,n):
        return sum( SP.sign()*\
                Cohomology4d.total_chern(VectorBundle4d.character(SP, weight))*\
                Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP)) for SP in list(pP4ds.with_num_boxes(n)))
    
    def Total_Segre(weight,n):
        return sum( SP.sign()*\
                Cohomology4d.total_chern(-VectorBundle4d.character(SP, weight))*\
                Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP)) for SP in list(pP4ds.with_num_boxes(n)))
    
    def Chern_Char(weight,n):
        return sum( SP.sign()*\
                SR(VectorBundle4d.character(SP, weight))*\
                SR(Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP))) for SP in list(pP4ds.with_num_boxes(n)))
    
    
    def Chern_Num(n,w1=w1,w2=w2,w3=w3,deg=0):
        total=0
        for SP in list(pP4ds.with_num_boxes(n)):
            seg = degn(Vertex4d.total_chern_vb(SP,w1,w2,w3)(t1=t1*b,t2=t2*b,t3=t3*b),n+deg)*b^(n+deg)
            add =SP.sign()*seg*Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP))(t1=t1*b,t2=t2*b,t3=t3*b)
            total+=add
        return total
    
    def Chern_with_sign(n,sign):
        total=0
        for i in range(len(list(pP4ds.with_num_boxes(n)))):
            SP=list(pP4ds.with_num_boxes(n))[i]
            seg = degn(Vertex4d.total_chern_vb(SP,w1,w2,w3)(t1=t1*b,t2=t2*b,t3=t3*b),n)*b^n
            add =sign[i]*seg*Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP))(t1=t1*b,t2=t2*b,t3=t3*b)
            total+=add
        return total
    
    def Segre_Num(n,w1=w1,w2=w2,w3=w3,deg=0):
        total=0
        for SP in list(pP4ds.with_num_boxes(n)):
            seg = degn(Vertex4d.total_segre_vb(SP,w1,w2,w3)(t1=t1*b,t2=t2*b,t3=t3*b),n+deg)*b^(n+deg)
            add =SP.sign()*seg*Cohomology4d.top_chern(-Vertex4d.sqrtTvir(SP))(t1=t1*b,t2=t2*b,t3=t3*b)
            total+=add
        return total
    
    def determinant_vb(partition,n,w1=w1,w2=w2,w3=w3):
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        det = KTheory.determinant(Q)^2*(SR(x1)^w1 * SR(x2)^w2 * SR(x3)^w3)^n*(SR(x1)^w4 * SR(x2)^w5 * SR(x3)^w6)^n
        return det(x1=exp(t1*b),x2=exp(t2*b),x3=exp(t3*b))
    
    def total_segre_vb(partition,w1=w1,w2=w2,w3=w3):
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        roots = []
        for coeff, mon in list(Q):
            wt = Cohomology4d.from_monomial(mon)
            roots += (coeff) * [wt+w1*t1+w2*t2+w3*t3]
            roots += (coeff) * [wt+w4*t1+w5*t2+w6*t3]
        total = prod(1/(1+r) for r in roots)
        return total
        
    def total_chern_vb(partition,w1=w1,w2=w2,w3=w3):
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        roots = []
        for coeff, mon in list(Q):
            wt = Cohomology4d.from_monomial(mon)
            roots += (coeff) * [wt+w1*t1+w2*t2+w3*t3]
            roots += (coeff) * [wt+w4*t1+w5*t2+w6*t3]
        total = prod((1+r) for r in roots)
        return total
    
    def top_chern_vb(partition,w1=w1,w2=w2,w3=w3):
        Q = partition.character(x1, x2, x3, x4=1/x1*1/x2*1/x3)
        roots = []
        for coeff, mon in list(Q):
            wt = Cohomology4d.from_monomial(mon)
            roots += (coeff) * [wt+w1*t1+w2*t2+w3*t3]
            roots += (coeff) * [wt+w4*t1+w5*t2+w6*t3]
        total = prod(r for r in roots)
        return total
    
    def Verlinde_Num(n,w1=w1,w2=w2,w3=w3,deg=0):
        total=0
        for SP in list(pP4ds.with_num_boxes(n)):
            add=SP.sign()*\
                deg0(((KTheory.measure_unsymmetrized(Vertex4d.sqrtTvir(SP))(x1=exp(t1*b),x2=exp(t2*b),x3=exp(t3*b)))*\
                (Vertex4d.determinant_vb(SP,n,w1=w1,w2=w2,w3=w3))).taylor(b,0,3))
            total+=add
        return total
    
    def Verlinde_Num_inv(n,w1=w1,w2=w2,w3=w3):
        total=0
        for SP in list(pP4ds.with_num_boxes(n)):
            add=SP.sign()*\
                deg0(((KTheory.measure_unsymmetrized(Vertex4d.sqrtTvir(SP))(x1=exp(t1*b),x2=exp(t2*b),x3=exp(t3*b)))*\
                (1/Vertex4d.determinant_vb(SP,n,w1=w1,w2=w2,w3=w3))).taylor(b,0,2))
            total+=add
        return total
    
    
def deg0(f):
    g=f.taylor(b,0,0)
    L=g.coefficients()
    if L[len(L)-1][1]!=0:
        return 0
    return L[len(L)-1][0]

def degn(f,n):
    g=f.taylor(b,0,n)
    L=g.coefficients()
    if L[len(L)-1][1]!=n:
        return 0
    return L[len(L)-1][0]
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
