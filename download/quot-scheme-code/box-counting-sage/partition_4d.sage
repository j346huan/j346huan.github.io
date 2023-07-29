"""
4d partitions with legs.
"""
from six import add_metaclass

from sage.structure.list_clone import ClonableElement
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.combinat.partition import Partition
from sage.rings.infinity import PlusInfinity

load("partition_3d.sage")
load("setup.sage")
load("setup_4d.sage")
    
    
@add_metaclass(InheritComparisonClasscallMetaclass)
class Partition4d(ClonableElement):
    r"""
    
    A solid (4d) partition is a sequence $\pi=\{\pi_{ijk}\}_{i,j,k\geq 1}$ of integers (possibly infinite) satisfying
    $$\pi_{ijk}\geq \pi_{i+1,j,k}, \pi_{i,j+1,k}, \pi_{i,j,k+1}$$
    Can be visualized as boxes in $\RR^4$ where $\pi_{ijk}$ is the height in the $x_4$-axis. It may have legs that extend in each axis.

    INPUT:

    - ``boxes`` -- list of coordinates `(i, j, k, l)` of additional boxes
      which are not part of the three pre-existing legs.
    
    - ``lamb``, ``mu``, ``nu``, ``rho`` -- 3d partitions specifying the profiles
      of the legs $\lambda=\{\lambda_{jk}\}, \mu=\{\mu{ik}\}, \nu=\{\nu{ij}\}, \rho=\{\rho_{ij}\}$.
      extending in $x_1,x_2,x_3,x_4$ directions resepctively (so the sequence for $\lambda,\mu,\nu$ are height in $x_4$ whereas $\rho$ is in direction $x_3$).
    
    EXAMPLES::
    
    
    
    """
    @staticmethod
    def __classcall_private__(cls, boxes, lamb=None, mu=None, nu=None, rho=None, check=True):
        """
        Constructs a 4d partition with legs with the appropriate parent.
        """
        if isinstance(boxes, cls):
            return boxes
        
        if isinstance(boxes, (list, tuple)):
            if all(isinstance(box, tuple) and len(box) == 4 for box in boxes):
                return Partitions4d(lamb, mu, nu, rho,check)(boxes, check)

        raise ValueError("first argument must be a list of (i, j, k, l)")
    
    def __init__(self, parent, boxes, check=True):
        """
        Initializes ``self``.

        Set ``check`` (default: True) to False to omit checking
        that the input ``boxes`` forms a valid solid partition.
        """
        self._lamb = parent._lamb
        self._mu = parent._mu
        self._nu = parent._nu
        self._rho = parent._rho
        
        self._noleg = ((0,0,0) not in self._lamb) and ((0,0,0) not in self._mu) and ((0,0,0) not in self._nu) and ((0,0,0) not in self._rho)

        ClonableElement.__init__(self, parent)

        self._Nx1 = parent._min_Nx1
        self._Nx2 = parent._min_Nx2
        self._Nx3 = parent._min_Nx3
        self._Nx4 = parent._min_Nx4
        
        self._boxes = set()
        for box in boxes:
            self._add_box_in_place(*box)

        self.set_immutable()
        if check:
            self.check()

    def check(self):
        """
        Check that ``self`` is a valid solid partition with given legs.
        
        The boxes in the legs automatically satisfy this condition.
        """
        for (i, j, k, l) in self._boxes:
            if not self._is_box_valid(i, j, k, l) or \
               self._in_num_legs(i, j, k, l) > 0:
                raise ValueError("invalid box (%s, %s, %s)" % (i, j, k))
        
    def _is_box_valid(self, i, j, k, l):
        r"""
        Check that it is valid to have a box in ``self`` at `(i, j, k, l)`.

        This means that a box at `(i, j, k, l)` must have neighboring boxes
        at `(i, j, k, l-1)` and `(i, j, k-1, l)` and `(i, j-1, k, l)` and `(i-1, j, k, l)`.
        """
        return ((l == 0 or (i, j, k,l-1) in self) and
                (k == 0 or (i, j, k-1,l) in self) and
                (j == 0 or (i, j-1, k,l) in self) and
                (i == 0 or (i-1, j, k,l) in self))
        
    def __contains__(self, x):
        """
        Checks whether there is a box at ``x=(i,j,k,l)``.
        """
        if not isinstance(x, (tuple, list)):
            return False
        if len(x) != 4:
            return False
        
        return (self._in_num_legs(*x) > 0 or x in self._boxes)

    def _in_num_legs(self, i, j, k, l):
        """
        Returns the number of legs that `(i, j, k, l)` belongs to.
        """
        return self._exists_in_legs(i, j, k, l).count(True)

    def _exists_in_legs(self, i, j, k, l):
        """
        Returns the legs that `(i, j, k, l)` belongs to.
        """
        return [self._exists_in_lamb(i, j, k, l),
                self._exists_in_mu(i, j, k, l),
                self._exists_in_nu(i, j, k, l),
                self._exists_in_rho(i, j, k, l)]

    def _exists_in_lamb(self, i, j, k, l):
        r"""
        Checks whether `(i, j, k, l)` is a box in the infinite leg `\lambda`.
        """
        return (j,k,l) in self._lamb
        
    def _exists_in_mu(self, i, j, k, l):
        r"""
        Checks whether `(i, j, k, l)` is a box in the infinite leg `\mu`.
        """
        return (i,k,l) in self._mu

    def _exists_in_nu(self, i, j, k, l):
        r"""
        Checks whether `(i, j, k, l)` is a box in the infinite leg `\nu`.
        """
        return (i,j,l) in self._nu
    
    def _exists_in_rho(self, i, j, k, l):
        r"""
        Checks whether `(i, j, k, l)` is a box in the infinite leg `\nu`.
        """
        return (i,j,k) in self._rho

    def __repr__(self):
        """
        Return a string representation of ``self``. Point-like if it has no legs, curve-like if legs have finite sizes (legs have no legs as 3d partitions)
        """
        if self._noleg:
            return "point-like solid partition with boxes %s" % list(self._boxes)
        else:
            return "curve-like solid partition with legs %s, %s, %s, %s and extra boxes %s" % \
                    (self._lamb, self._mu, self._nu, self._rho, list(self._boxes))
            

    def __hash__(self):
        """
        Return the hash of ``self``.
        """
        return hash(self.parent()) ^^ hash(frozenset(self._boxes))

    def __copy__(self):
        """
        Return a copy of ``self``.
        """
        # Manually copy boxes, otherwise res._boxes is self._boxes
        res = ClonableElement.__copy__(self)
        res._boxes = self._boxes.copy()

        return res
        
    def __eq__(self, other):
        """
        Return true if ``self`` is the same 3d partition as ``other``.
        """
        if isinstance(other, self.__class__):
            return (self.parent() == other.parent() and
                    self._boxes == other._boxes)
        return False

    def __ne__(self, other):
        """
        Return true if ``self`` is not the same 3d partition as ``other``.
        """
        return not self.__eq__(other)
    
    def plot(self):
        """
        Plot ``self`` as a Graphics3d object.
        """
        Nx1, Nx2, Nx3, Nx4 = self.bounding_box()
        Bx1, Bx2, Bx3 = max(10, Nx1+5), max(10, Nx2+5), max(10, Nx3+5)
        plotfactor=0
        if self._noleg:
            plotfactor=1
        else:
            plotfactor=0.8
        
        from sage.plot.plot3d.plot3d import axes
        plot = axes(max(max(Bx1, Bx2), Bx3)+1, 3, color='black')
        
        from sage.plot.plot3d.shapes import ColorCube
        for b in self.boxes(Nx1=Bx1, Nx2=Bx2, Nx3=Bx3, Nx4=1):
            h = self.height(b[0],b[1],b[2])
            if h==-1: raise ValueError("this box should not exist")
            pct = 1 if h==-2 else min(1, h/max(1,(Nx4-1)))*plotfactor
            pct_diff = 1.0 - pct
            red_color = min(1, pct*2)
            green_color = min(1, pct_diff*2)
            col = (red_color, green_color, 0)
            cube = ColorCube([.5,.5,.5], (col,col,col), opacity=0.3)
            plot += cube.translate((b[0],b[1],b[2]))

        plot.show(frame=False, axes=True, aspect_ratio=1)
        
    def height(self,i,j,k):
        r"""
        Return value of $\pi_{ijk}-1$, which is the height in x4-axis of the boxes.
        """
        if self._exists_in_rho(i, j, k,0):
            return -2
        else: 
            l=0
            while (i,j,k,l) in self: 
                l+=1
            return l-1

    def boxes(self, Nx1=PlusInfinity, Nx2=PlusInfinity, Nx3=PlusInfinity, Nx4=PlusInfinity):
        r"""
        Iterate through all boxes in ``self`` which are contained in
        the bounding box `[0, Nx1) x [0, Nx2) x [0, Nx3) x [0, Nx4)`.
        """
        if (0, 0, 0, 0) not in self or Nx1 <= 0 or Nx2 <= 0 or Nx3 <= 0 or Nx4 <= 0:
            return 
        stack = [(0, 0, 0)]
        seen = {}
        while stack:
            (i, j, k) = stack.pop()
            for l in range(Nx4):
                if (i, j, k, l) not in self:
                    break
                yield (i, j, k, l)

            if (i+1 < Nx1) and ((i+1, j, k) not in seen) and ((i+1, j, k, 0) in self):
                seen[(i+1, j, k)] = True
                stack.append((i+1,j,k))
            if (j+1 < Nx2) and ((i, j+1, k) not in seen) and ((i, j+1, k, 0) in self):
                seen[(i, j+1, k)] = True
                stack.append((i,j+1,k))
            if (k+1 < Nx3) and ((i, j, k+1) not in seen) and ((i, j, k+1, 0) in self):
                seen[(i, j, k+1)] = True
                stack.append((i,j,k+1))

    def volume(self):
        r"""
        Returns the *normalized* volume of ``self``.

        The normalized volume of a 4d partition `\pi` with legs
        `\lambda`, `\mu`, `\nu`, `\rho` is the quantity

        .. MATH::

            #\{\pi \cap [0, N]^4\} - (N+1) (|\lambda| + |\mu| + |\nu|+|\rho|)

        which is independent of `N` for sufficiently large `N`.
        """
        return self.parent().minimal_volume() + len(self._boxes)
    
    def bounding_box(self):
        r"""
        Returns the box `[0, Nx) x [0, Ny) x [0, Nz)` beyond which there
        are only boxes belonging to a single asymptotic leg.
        """
        return (self._Nx1, self._Nx2, self._Nx3, self._Nx4)

    def _unnormalized_character(self, x1=Default4d.x1, x2=Default4d.x2, x3=Default4d.x3, x4=Default4d.x4):
        r"""
        Returns the character associated to ``self`` (see :meth:`character`),
        multipled by the additional factor `(1-x1)(1-x2)(1-x3)(1-x4)`.

        This guarantees the result is a Laurent polynomial.
        """
        Nx1, Nx2, Nx3, Nx4 = self._Nx1, self._Nx2, self._Nx3, self._Nx4

        char = sum(x1**i * x2**j * x3**k * x4**l
                   for (i,j,k,l) in self.boxes(Nx1=Nx1, Nx2=Nx2, Nx3=Nx3, Nx4=Nx4))
        char *= (1-x1)*(1-x2)*(1-x3)*(1-x4)
        
        char += self.leg_character_lamb(x1,x2,x3,x4) * x1**Nx1 * (1-x2)*(1-x3)*(1-x4)
        char += self.leg_character_mu(x1,x2,x3,x4) * x2**Nx2 * (1-x3)*(1-x1)*(1-x4)
        char += self.leg_character_nu(x1,x2,x3,x4) * x3**Nx3 * (1-x1)*(1-x2)*(1-x4)
        char += self.leg_character_rho(x1,x2,x3,x4) * x4**Nx4 * (1-x1)*(1-x2)*(1-x3)

        return char

    def character(self, x1=Default4d.x1, x2=Default4d.x2, x3=Default4d.x3, x4=Default4d.x4):
        r"""
        Return the character associated to ``self``, in variables `x1, x2, x3`.

        The character of a 3d partition `\pi` is

        .. MATH::

            \sum_{(i,j,k,l) \in \pi} x_1^i x_2^j x_3^k x_4^l

        In general, it lives in the fraction field of polynomials
        in `x1, x2, x3,x4`.
        """
        if self._noleg:
            Nx1, Nx2, Nx3, Nx4 = self._Nx1, self._Nx2, self._Nx3, self._Nx4
            return sum(x1**i * x2**j * x3**k * x4**l
                   for (i,j,k,l) in self.boxes(Nx1=Nx1, Nx2=Nx2, Nx3=Nx3, Nx4=Nx4))
        else:
            return self._unnormalized_character(x1,x2,x3,x4) / ( (1-x1)*(1-x2)*(1-x3)*(1-x4) )
        
        
    def sign_sigma(self, i):
        r"""
        Return sigma(pi)=|pi|+number of (a_1,...,a_4) in pi such that a_j=a_k=a_l<a_i, where 1<=i<=4 is the input.
        """
        i=i-1
        sigma=0
        if self._noleg:
            sigma+=len(self._boxes)
            for w in self._boxes:
                if ( (w[(i+1) % 4]==w[(i+2) % 4]) and (w[(i+2) % 4]==w[(i+3) % 4]) and (w[(i+3) % 4]<w[i % 4]) ):
                    sigma+=1
            return sigma
        else:
            raise NotImplementedError("The partition needs to be finite")
        
    def sign(self, i=4):
        r"""
        Return the canonical sign of `self` used by Monavari.
        sigma(pi)=|pi|+number of (a_1,...,a_4) in pi such that a_j=a_k=a_l<a_i, where 1<=i<=4 is the input.
        """
        return (-1)^self.sign_sigma(i)
    
    
    
    def legs(self):
        r"""
        Returns the legs `\lambda`, `\mu`, `\nu`, `\rho` of ``self``.
        """
        return self.parent().legs()

    def leg_character_lamb(self, x1, x2, x3,x4):
        r"""
        Returns the character associated to the leg `\lambda`.
        """
        return self._lamb.character(x2,x3,x4)

    def leg_character_mu(self, x1, x2, x3,x4):
        r"""
        Returns the character associated to the leg `\mu`.
        """
        return self._mu.character(x1,x3,x4)

    def leg_character_nu(self, x1, x2, x3,x4):
        r"""
        Returns the character associated to the leg `\nu`.
        """
        return self._nu.character(x1,x2,x4)

    def leg_character_rho(self, x1, x2, x3,x4):
        r"""
        Returns the character associated to the leg `\rho`.
        """
        return self._rho.character(x1,x2,x3)

    def _add_box_in_place(self, i, j, k, l):
        r"""
        Add a box at `(i, j, k, l)` to ``self`` in place.

        This is an internal method. Users should use :meth:`add_box` instead.
        """
        self._require_mutable()

        self._boxes.add( (i,j,k,l) )

        self._Nx1 = max(i+1, self._Nx1)
        self._Nx2 = max(j+1, self._Nx2)
        self._Nx3 = max(k+1, self._Nx3)
        self._Nx4 = max(l+1, self._Nx4)

    def add_box(self, i, j, k, l, check=True):
        r"""
        Return a new 3d partition which is ``self`` with an
        extra box at `(i, j, k, l)`.

        Set ``check=False`` to skip checking that adding such a box is valid.

        """
        with self.clone(check=check) as new_PP:
            new_PP._add_box_in_place(i, j, k, l)

        return new_PP

    def addable_boxes(self):
        r"""
        Iterates through all `(i, j, k)` where it is valid to
        add an extra box to ``self``.
        """
        for i in range(self._Nx1 + 1):
            for j in range(self._Nx2 + 1):
                for k in range(self._Nx3 + 1):
                    for l in range(self._Nx4 + 1):
                        if (i, j, k, l) not in self and self._is_box_valid(i, j, k,l):
                            yield (i, j, k, l)
                            break # can't add higher boxes

    def partitions_with_one_more_box(self):
        """
        Iterates through all partitions with one more box than ``self``
        """
        for (i, j, k, l) in self.addable_boxes():
            yield self.add_box(i, j, k, l, check=False)

class Partitions4d(UniqueRepresentation, Parent):
    """
    The set of 4d partitions with specified legs.

    """
    Element = Partition4d

    @staticmethod
    def __classcall_private__(cls, lamb=None, mu=None, nu=None, rho=None, check=True):
        lamb = lamb if isinstance(lamb,Partition3d) else Partition3d([])
        mu = mu if isinstance(mu,Partition3d) else Partition3d([])
        nu = nu if isinstance(nu,Partition3d) else Partition3d([])
        rho = rho if isinstance(rho,Partition3d) else Partition3d([])
        return cls.__classcall__(cls, lamb, mu, nu, rho,check)
    
    def __init__(self, lamb, mu, nu, rho, check=True):
        r"""
        Initializes ``self``.
        """
        Parent.__init__(self, category=InfiniteEnumeratedSets())
        
        self._lamb = lamb
        self._mu = mu
        self._nu = nu
        self._rho = rho

        # Minimum size of bounding box with given legs
        self._min_Nx1 = max(self._mu._Nx, self._nu._Nx, self._rho._Nx)
        self._min_Nx2 = max(self._lamb._Nx, self._nu._Ny, self._rho._Ny)
        self._min_Nx3 = max(self._mu._Ny, self._nu._Ny, self._rho._Nz)
        self._min_Nx4 = max(self._mu._Nz, self._nu._Nz, self._rho._Nz)

        # Data of minimal configuration with given legs
        self._min_vol = None
        self._compute_minimal_volume()
        
        if check:
            self.check()

        # Cache all partitions with k additional boxes once we've computed
        # them all for a given k. This saves work.
        self._generated_up_to = 0
        self._cache = [set([self.minimal_element()])]

    def check(self):
        """
        Check that given legs are finite size so that normalized volume is well-defined.
        """
        if not (self._lamb in Partitions3d([]) and self._mu in Partitions3d([]) and self._nu in Partitions3d([]) and self._rho in Partitions3d([])):
            raise ValueError("not a point-like or curve-like partition")

    def _an_element_(self):
        """
        Returns a 4d partition in ``self``.
        """
        return self.minimal_element()
        
    def minimal_element(self):
        """
        Returns the element with the smallest volume in ``self``.
        """
        return self.element_class(self, boxes=[])

    def minimal_volume(self):
        """
        Returns the minimal possible volume of an element in ``self``.
        """
        return self._min_vol

    def _compute_minimal_volume(self):
        """
        Computes the *normalized* volume of the minimal configuration
        of boxes with given legs. Called on initialization. 
        """
        PP = self.minimal_element()
        vol = 0
        for (i, j, k, l) in PP.boxes(Nx1=self._min_Nx1, Nx2=self._min_Nx2, Nx3=self._min_Nx3, Nx4=self._min_Nx4):
            vol += 1 - PP._in_num_legs(i, j, k, l)
        self._min_vol = vol

    def __contains__(self, x):
        """
        Check if ``x`` is contained in ``self``.
        """
        if isinstance(x, self.element_class):
            return x.parent() == self
        else:
            return False

    def __repr__(self):
        """
        Return a string representation of ``self``.
        """
        if not self._lamb and not self._mu and not self._nu and not self._rho:
            return "Finite 4d partitions"
        else:
            return "4d partitions with legs %s, %s, %s, %s" % \
                (self._lamb, self._mu, self._nu, self._rho)

    def _hash_(self):
        """
        Return the hash of ``self``.
        """
        return hash(self._lamb) ^^ hash(self._mu) ^^ hash(self._nu) ^^ hash(self._rho)



    def legs(self):
        r"""
        Returns the legs `\lambda`, `\mu`, `\nu`, `\rho` of ``self``.
        """
        return self._lamb, self._mu, self._nu, self._rho

    def _compute_next_partitions(self):
        r"""
        Compute all 4d partitions in ``self`` with volume one more
        than what has already been computed and cached.
        """
        new_PPs = set()
        for PP in self._cache[-1]:
            for new_PP in PP.partitions_with_one_more_box():
                if new_PP not in new_PPs:
                    new_PPs.add(new_PP)
        self._cache.append(new_PPs)
        self._generated_up_to += 1

    def with_num_boxes(self, n):
        r"""
        Iterates through all elements of ``self`` with specified legs
        and `n` extra boxes.
        """
        while self._generated_up_to < n:
            self._compute_next_partitions()

        for PP in self._cache[n]:
            yield PP

    def up_to_num_boxes(self, n):
        r"""
        Iterates through all elements of ``self`` with specified legs
        and up to (and including) `n` extra boxes.

        EXAMPLES::

            sage: PPs_finite = Partitions3d([], [], [])
            sage: list(PPs_finite.up_to_num_boxes(1))
            [3d partition with boxes [], 3d partition with boxes [(0, 0, 0)]]
            sage: [len(list(PPs_finite.up_to_num_boxes(k))) for k in (0..6)]
            [1, 2, 5, 11, 24, 48, 96]
        """
        k = 0
        while k <= n:
            for PP in self.with_num_boxes(k):
                yield PP
            k += 1

    def __iter__(self):
        r"""
        Iterates through all eleemnts of ``self``, in order of increasing
        volume.
        """
        for PP in self.up_to_num_boxes(PlusInfinity):
            yield PP

    def random_element_with_num_boxes(self, n):
        r"""
        Picks a random element with volume `n` in ``self``.

        NOTE: distribution is *not* uniform!

        ALGORITHM: pick a box to add uniformly at random (among all
        possible boxes to add), and do this `n` times.
        """
        PP = self.minimal_element()
        for _ in range(n):
            addable_boxes = list(PP.addable_boxes())

            import random
            box = random.choice(addable_boxes)

            PP = PP.add_box(*box)

        return PP
    
