load("setup.sage")

KT_vars = ['x','y']
KT_ring = LaurentPolynomialRing(QQ, KT_vars)

coho_vars = ['t','m']
coho_ring = LaurentPolynomialRing(QQ, coho_vars)

x,y=KT_ring.gens()
t,m = coho_ring.gens()
z=var('z')
b=var('b')
W=var('w')
V=var('v')
L=var('l')



def character(p,x=x,y=y):
    return sum(y^(-r) * x^(-c) for r, c in p.cells())

def character_vb(p, w,x=x,y=y):
    Q = character(p,x,y)
    return sum(Q * x^(w[2*i]) * y^(w[2*i+1]) for i in range(len(w)/2))

def dual(f):
    R = f.parent()
    g= R.zero()
    for exp, coeff in f.dict().items():
        g+= R({exp.emul(-1): coeff})
    return g

def tangent(p,x=x,y=y):
    total=0
    for r,c in p.cells():
        arm=p[r]-c-1
        leg=p.conjugate()[c]-r-1
        total+=y^(-leg)*x^(arm+1)+y^(leg+1)*x^(-arm)
    return total

def canonical_bundle(p,x=x,y=y):
    return character_vb(p, (-1,-1),x,y)


def structure_sheaf(p,x=x,y=y):
    return character_vb(p, (0,0),x,y)

def top_chern(f):
    numer, denom = [], []
    for coeff, mon in list(f):
        wt = from_monomial(mon)
        #if wt==0:
            #continue
        if coeff > 0:
            numer += (coeff) * [wt]
        elif coeff < 0:
            denom += (-coeff) * [wt]
    
    return coho_ring.fraction_field()(prod(numer) / prod(denom))

def determinant(f):
    if f in ZZ:
        return 1
    else:
        return prod((mon)^coeff for coeff, mon in f)

def from_monomial(m):
    return sum(m.degree(KT_ring.gen(i)) * coho_ring.gen(i) for i in range(len(coho_ring.gens())))

def from_character(f):
    numer, denom = [], []

    for coeff, mon in list(f):
        wt = from_monomial(mon)
        if coeff > 0:
            numer += (coeff) * [wt]
        elif coeff < 0:
            denom += (-coeff) * [wt]
    return numer, denom

def measure_unsymmetrized(f, inv=True):
    """
    computes 1/(1-x^-1) for K-thy class x. If inv=false, returns 1/(1-x)
    """
    R = f.parent()
    
    if f.parent() is ZZ:
        L = [(ZZ(f), 1)]
    else:
        L = list(f)

    numer, denom = R.one(), R.one()
    for coeff, monomial in L:
        if inv:
            term = 1 - monomial^-1
        else:
            term = 1 - monomial
        if monomial==1:
            term = 0
        if coeff < 0:
            numer *= term ** (-coeff)
        elif coeff > 0:
            denom *= term ** coeff
    return numer / denom

def total_chern(f):
    numer, denom = from_character(f)
    new_numer=[i+1 for i in numer]
    new_denom=[i+1 for i in denom]
    return coho_ring.fraction_field()(prod(new_numer+[1]) / (prod(new_denom)))


def total_chern_vb(p):
    Q = character(p,x,y)
    roots = []
    vb_weight = W
    for coeff, mon in list(Q):
        wt = from_monomial(mon)
        roots += (coeff) * [wt+vb_weight]
    total = prod((1+r) for r in roots)
    return total

def total_segre_vb(p):
    Q = character(p,x,y)
    roots = []
    vb_weight = W
    for coeff, mon in list(Q):
        wt = from_monomial(mon)
        roots += (coeff) * [wt+vb_weight]
    total = prod(1/(1+r) for r in roots)
    return total

def determinant_vb(p,n):
    Q = character(p,x,y)
    det = determinant(Q)*(exp(W*n))
    return det

def determinant_vb_rank_2(p,n):
    Q = character(p,x,y)
    det = (determinant(Q)^2)*(exp((W+V)*n))
    return det

def total_chern_vb_rank_2(p):
    Q = character(p,x,y)
    roots = []
    for coeff, mon in list(Q):
        wt = from_monomial(mon)
        roots += (coeff) * [wt+W]
        roots += (coeff) * [wt+V]
    total = prod((1+r) for r in roots)
    return total


def total_segre_vb_rank_2(p):
    Q = character(p,x,y)
    roots = []
    for coeff, mon in list(Q):
        wt = from_monomial(mon)
        roots += (coeff) * [wt+W]
        roots += (coeff) * [wt+V]
    total = prod(1/(1+r) for r in roots)
    return total

def Chern_Num(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_chern_vb(p)
        total+=add
    return total

def Chern_Num_rank_2(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_chern_vb_rank_2(p)
        total+=add
    return total

def Chern_Num_vir(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_chern_vb(p)*top_chern(dual(canonical_bundle(p,x,y)))
        total+=add
    return total

def Chern_Num_vir_rank_2(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_chern_vb_rank_2(p)*top_chern(dual(canonical_bundle(p,x,y)))
        total+=add
    return total

def Segre_Num(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_segre_vb(p)
        total+=add
    return total

def Segre_Num_vir(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_segre_vb(p)*top_chern(dual(canonical_bundle(p,x,y)))
        total+=add
    return total

def Segre_Num_vir_rank_2(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*total_segre_vb_rank_2(p)*top_chern(dual(canonical_bundle(p,x,y)))
        total+=add
    return total


def Verlinde_Num(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p))*\
            determinant_vb(p,n)
        total+=add
    return total



def Verlinde_Num_inv(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p))*\
            (1/determinant_vb(p,n))
        total+=add
    return total



def Verlinde_Num_vir(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p)-dual(canonical_bundle(p,x,y)))*\
            determinant_vb(p,n)
        total+=add
    return total

def Verlinde_Num_vir_rank_2(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p)-dual(canonical_bundle(p,x,y)))*\
            determinant_vb_rank_2(p,n)
        total+=add
    return total

def Verlinde_Num_vir_inv(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p))*\
            (1/determinant_vb(p,n))*\
            measure_unsymmetrized(-canonical_bundle(p,x,y),inv=False)
        total+=add
    return total

def measure_z_vb_1(p):
    f = character_vb_rank_1(p,x,y)
    L = f.expand().operands()
    if p.size()==1:
        L=[exp(W),]
    total=1
    for monomial in L:
        term = 1 - monomial*z
        total*=term
    return total

def custom_invariant(n):
    total=0
    for p in Partitions(n):
        add=measure_unsymmetrized(tangent(p)-dual(canonical_bundle(p,x,y)))*\
            determinant(dual(character_vb(p,(0,0),x,y)))*\
            measure_z_vb_1(p)
        total+=add
    return (-1)^n*total

def character_vb_rank_2(p,x=x,y=y):
    Q = character(p,x,y)
    return Q * (exp(W)+exp(V))

def character_vb_rank_1(p,x=x,y=y):
    Q = character(p,x,y)
    return Q * (exp(W))


def measure_z_vb(p):
    f = character_vb_rank_2(p,x,y)
    L = f.expand().operands()
    total=1
    for monomial in L:
        term = 1 - monomial*z
        total*=term
    return total

def Master_Partition_rank_2(n):
    total=0
    for p in Partitions(n):
        add=determinant(dual(character_vb(p,(0,0),x,y)))*\
            measure_unsymmetrized(tangent(p))*\
            measure_z_vb(p)
        total+=add
    return (-1)^n*total

def DT_Num(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))
        total+=add
    return total

def DT_Num_vir(n):
    total=0
    for p in Partitions(n):
        add=top_chern(-tangent(p))*top_chern(dual(canonical_bundle(p,x,y)))
        total+=add
    return total

def degn(f,n,b=b):
    g=f.taylor(b,0,n+2)
    L=g.coefficients(b)
    for i in range(len(L)):
        if L[i][1]==n:
            return L[i][0]
    return 0
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
