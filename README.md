TTIE - Type Theory with Indexed Equality
---------------------------------------

A demo interpreter and type checker of a type theory with interval indexed equality types.

The indexed equality type looks like this (in Agda notation):

    data Interval : Type where
      i0 : Interval
      i1 : Interval
      i01 : i0 == i1
    
    data Eq (A : Interval -> Type) (A i0) (A i1) : Type where
      refl : (x : (i : Interval) -> A i) -> Eq A (x i0) (x i1)

We write the binders for intervals as a subscript, so `Eq_i (A i) x y`.

Syntax
------

The syntax is modeled after Agda and Haskell:

    -- a comment
    {- also a comment -}
    variable
    _                     -- a hole, filled in by unification
    
    Type : Type1          -- the type of types
    
    tt : Unit             -- built in unit type, with constructor tt
    
    Unit -> Unit          -- function type
    (A : Type) -> A -> A  -- dependent function type
    {A : Type} -> A -> A  -- implicit arguments
    forall x -> B x       -- the same as (x : _) -> B x
    ∀ x. B x              -- the same
    \x -> e               -- lambdas / anonymous functions
    \(x : A) -> e         -- with type annotation
    (x : A) => e          -- same
    f x                   -- function application
    f {x}                 -- explicit application to an implicit argument
    
    (x : A) * B x         -- dependent sums (pairs)
    {x : A} * B x         -- with implicit arguments (to model existentials)
    exists x -> B x       -- the same as (x : _) * B x
    ∃ x. B x              -- the same
    x , y                 -- construct a pair
    proj1 x               -- first projection of a pair
    proj2 x               -- second projection
    {proj1} x             -- projection of an implicit pair/existential
    {x} , y               -- explicit construction of an implicit pair
    
    i0
    i1 : Interval         -- The interval has values i0 and i1
    i01 : Eq _ i0 i1      -- the path between i0 and i1
    refl_i i              -- the same
    iflip i               -- sends i0 to i1 and vice-versa
    iand i j              -- i1 if i and j are both i1
    
    Eq A x y              -- type of equality proofs of x and y of type A
    Eq_i (A i) x y        -- indexed equality between x : A i0 and y : A i1
    x == y                -- sugar for equality type
    refl x                -- reflexivity at x
    refl_i (x i)          -- indexed version
    xy^i                  -- end point of a path, if xy : Eq _ x y, xy^i0 = x, xy^i1 = y, refl_i xy^i = xy
    iv x y xy i           -- desugared version of xy^i
    
    cast_i (A i) u v x    -- substitution: if (x : A u), the result has type (A v)
    fw_i (A i) x          -- short hand notation for cast_i (A i) i0 i1
    bw_i (A i) x          -- short hand notation for cast_i (A i) i1 i0
    
    data{left:A; right:B} -- A sum type, constructors have a single argument type
    value left x          -- A value of the above data type, you may need a type signature
    case x of {left y -> ..; right y -> ..} -- case analysis of a sum type
    data{}                -- The type with no constructors (bottom)

Declarations and commands look like

    name : Type
    name = expression
    
    :help
    :quit
    :type e
    :eval e
    :nf e
    :check e = e'

Remarks:
 * There is no support for function definitions with arguments, use lambdas instead.
 * Built in names like `Eq`, `proj1`, `cast`, etc. must always be fully applied.
 * Spaces around operators like `->` are usually required, because `-` can be part of a name.
 * There is no support for recursion yet.
 * Implicit projections have not yet been implemented.
 * Unification is often not very smart.

Usage
-----

The implementation comes with a REPL:

    $ cabal build
    $ dist/tie examples/Prelude.ttie

The unit tests from Tests.hs are also instructive

    $ cabal test

Examples
--------
Here is a proof that `fw ∘ bw = id`

    A : Type
    B : Type
    AB : Eq _ A B
    lemma : forall x. fw_i (AB^i) (bw_i AB^i x) == x
    lemma = \x -> refl_j (cast_i AB^i j i1 (cast_i AB^i i1 j x))

Proof of function extensionality:

    ext : ∀ {A : Type} {B : A → Type} {f g : (x : A) → B x} → (∀ x. f x == g x) → f == g
    ext = \fg → refl_i \x → (fg x)^i

