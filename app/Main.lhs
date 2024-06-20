Representing Bidirectional Proof Systems
========================================

Suppose we want to implement a bidirectional proof system in Haskell. How can we go about doing that? Well, there's many ways, but this post will try to highlight one particular form of especially shallow embedding, and emphasize the ways that it can be advantageous.

In particular, I want to look at three specific aspects that are especially convenient when an extremely shallow embedding is employed, and how this relates to the ergonomics of the implementation:

1. The ability to inspect a proof process
2. The ability to report errors conveniently
3. The ability to extend the proof system with additional tooling

First, some preamble nonsense that we can't silence.

> {-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, QuantifiedConstraints, UndecidableInstances #-}
> module Main where
> import Control.Monad.Trans.Maybe
> import Control.Monad.Except
> import Control.Monad.Identity
> import Control.Monad.State
> main :: IO ()
> main = do
>   print $ search (prove (Plus (Suc Zero) (Suc Zero)))
>   print $ search (prove (Minus (Suc (Suc Zero)) (Suc Zero)))
>   print $ search (prove (Minus (Suc Zero) (Suc (Suc Zero))))
>   print $ loggingSearch (prove (Plus (Suc Zero) (Suc Zero)))
>   print $ loggingSearch (prove (Minus (Suc (Suc Zero)) (Suc Zero)))
>   print $ loggingSearch (prove (Minus (Suc Zero) (Suc (Suc Zero))))
>   print $ runContextualSearch (prove (Plus (Suc Zero) (Suc Zero)))
>   print $ runContextualSearch (prove (Minus (Suc (Suc Zero)) (Suc Zero)))
>   print $ runContextualSearch (prove (Minus (Suc Zero) (Suc (Suc Zero))))



A Toy Proof System
------------------

For the sake of simplicity, let's consider a toy proof system that consists of the Peano arithmetic. We choose this specifically because the relational definition and the standard functional definition have simple and clear relationships, and the latter is almost certainly familiar to everyone, requiring no explanation.

The judgment we will consider, then, is the ternary `sum` relation, whereby the meaning of `sum M N P` is supposed to be that the sum of M and N is P. That is to say, `sum M N P` is true if and only if `M + N = P` is also true. We define this judgment via the inference rules

```
--------- sum-0
sum 0 N N

      sum M N P
--------------------- sum-successor
sum (suc M) N (suc P)
```

Now, what goes into this proof system? Well, there are judgments -- here only one, namely, `sum M N P` -- and there are inference rules. There is also an implicit assumption that judgments aren't always provable, and so an attempt to prove something might fail. Also, there is an implicit reliance on unification and metavariables to constrain applicability of the rule, propagate information around, and so forth.

How shall we encode these various components into an implementation? Let's start with metavariables and unification: we'll eliminate them entirely, instead relying on mode assignments. Rather than dealing with `sum M N P` directly, we can perform a mode assignment analysis and find a handful of useful ones. In particular, we'll choose the first two components of the judgment to be input moded, and the third component to be output moded, and we'll refer to this version of the judgment as `plus M N P` to emphasize this. We'll also have `minus P N M`, which will correspond to subtraction, again moding the two first components as input and the last as output. Note that `M + N = P iff P - N = M`.

Now, how might we capture the judgments? A simple data type of judgments would suffice. Each input moded component of the judgment will be an argument to the constructors. But the output moded components aren't known upfront, and instead we'll make sure to index it by a phantom type corresponding to the sort of thing that the output moded components are. In this case, the output moded component is a single natural number. In a more sophisticated type system, it might be a term, or a type, or collections of things, etc.

What about representing an in-progress proof? Well there are many ways people have done this in the past. If we were using unification for information propagation, we might just maintain a list of goal judgments that constitute the as-of-yet unproven parts of the current in-progress proof. This would also provide us with a nice answer to the question of how to encode inference rules: we could say that the set of inference rules is just a function that maps every judgment to one (or maybe multiple) sets of premises that each would suffice to prove the judgment. But since we're using a bidirectional system in place of unification, we need something more like a telescope than a list. A telescope is just a list where the later contents can refer to the earlier contents in some way. This then answers the question about inference rules: we'll encode them as functions decomposing a judgment into a telescope!

Finally, how can we handle the possibility of failure? One traditional method is to symbolize failure by a big X above a judgment that can't be proven. We'll mirror this by ensuring that whatever our encoding of in-progress proofs is, it also includes the equivalent of that big X over a judgment.

So let's write this out explicitly:

> data ProofProcess g a where
>
>   -- done proving, with some output components
>   Done :: a -> ProofProcess g a
>
>   -- a premise to prove
>   Prove :: g b -> (b -> ProofProcess g a) -> ProofProcess g a
>
>   -- a possible failure
>   Failure :: ProofProcess g a
>
> class Decomposable g where
>   decompose :: g a -> ProofProcess g a

Those with keen eyes might recognize this as a variant of the freer monad. Those unfamiliar with that might want to read Kiselyov and Ishii's fantastic paper "Freer Monads, More Extensible Effects" (https://okmij.org/ftp/Haskell/extensible/more.pdf) for an overview of what freer monads are, but only after finishing this tutorial, of course!

Suffice it to say, this type of proof processes forms a monad, which will be very useful:

> instance Functor (ProofProcess g) where
>   fmap f (Done x) = Done (f x)
>   fmap f (Prove g k) = Prove g (fmap f . k)
>   fmap _ Failure = Failure
>
> instance Applicative (ProofProcess g) where
>   pure = Done
>   Done f <*> y = fmap f y
>   Prove g k <*> y = Prove g (\x -> k x <*> y)
>   Failure <*> _ = Failure
>
> instance Monad (ProofProcess g) where
>   Done x >>= f = f x
>   Prove g k >>= f = Prove g (\x -> k x >>= f)
>   Failure >>= _ = Failure
>
> prove :: g a -> ProofProcess g a
> prove g = Prove g Done
>
> failure :: ProofProcess g a
> failure = Failure

Before going any further with this, let's look at how we encode our toy proof system and get a feel for the parts:

> data Nat = Zero | Suc Nat
>   deriving (Show)
>
> data MathG a where
>   Plus :: Nat -> Nat -> MathG Nat
>   Minus :: Nat -> Nat -> MathG Nat
>
> instance Show (MathG a) where
>   showsPrec prec (Plus m n) = 
>     showParen (prec > 10) $ showString "Plus " . showsPrec 11 m . showString " " . showsPrec 11 n
>   showsPrec prec (Minus p n) =
>     showParen (prec > 10) $ showString "Minus " . showsPrec 11 p . showString " " . showsPrec 11 n
>
> instance Decomposable MathG where
>   decompose (Plus Zero n) = Done n
>   -- alternative just `return n`
>   decompose (Plus (Suc m) n) = Prove (Plus m n) (\p -> Done (Suc p))
>   -- alternatively just `do p <- prove (Plus m n) ; return (Suc p)` etc.
>   decompose (Minus p Zero) = Done p
>   -- `return p`
>   decompose (Minus Zero _) = Failure
>   -- `mzero`
>   decompose (Minus (Suc p) (Suc n)) = prove (Minus p n)


Having the proof system encoded like this isn't enough to make this an actual useful implementation of it, however. We still need a way to actually deploy the proof system to perform proof search:

> search :: Decomposable g => ProofProcess g a -> Maybe a
> search (Done x) = Just x
> search (Prove g k) =
>   do x <- search (decompose g)
>      search (k x)
> search Failure = Nothing

Now if we run a search, such as `search (prove (Plus (Suc Zero) (Suc Zero)))`, it will succeed with the sum as expected, and similarly for differences.

Let's look at a simulated trace of this process, just to get a feel for what's actually going on. We start with something like

```haskell
Prove (Plus (Suc Zero) (Suc Zero)) Done
```

One step of searching plus delta and beta reductions produces

```haskell
Prove (Plus Zero (Suc Zero)) Done >>= (\p' -> Done (Suc p'))
=
Prove (Plus Zero (Suc Zero)) (\p -> Done p >>= (\p' -> Done (Suc p')))
=
Prove (Plus Zero (Suc Zero)) (\p -> Done (Suc p))
```

Another step decomposes and we get

```haskell
Done (Suc Zero) >>= (\p -> Done (Suc p))
=
Done (Suc (Suc Zero))
```

Let's now make a modified search with logging of the intermediate goals:

> data Wrapped g where
>   Wrapped :: g a -> Wrapped g
>
> instance (forall a. Show (g a)) => Show (Wrapped g) where
>   showsPrec prec (Wrapped g) =
>     showParen (prec > 10) $ showString "Wrapped " . showsPrec 11 g
>
> loggingSearch :: Decomposable g => ProofProcess g a -> Maybe ([Wrapped g], a)
> loggingSearch (Done x) = return ([], x)
> loggingSearch (Prove g k) =
>   do (l, x) <- loggingSearch (decompose g)
>      (l', y) <- loggingSearch (k x)
>      return (Wrapped g:l++l', y)
> loggingSearch Failure = mzero

This only logs on the success cases, but we could log on failure too.

An alternative to this, which is probably more useful for error reporting specifically, is a contextual logging, rather than a sequential one. Instead of reporting all of the subgoals we've seen so far, we can instead report the path from the root goal down to the current failing goal:

> type Context g = [Wrappged g]
> type Contextual g = StateT (Context g) (Either (Context g))
> contextualSearch :: Decomposable g => ProofProcess g a -> Contextual g a
> contextualSearch (Done x) = return x
> contextualSearch (Prove g k) =
>   do modify (Wrapped g:)
>      x <- contextualSearch (decompose g)
>      modify tail
>      contextualSearch (k x)
> contextualSearch Failure =
>   do ctx <- get
>      throwError ctx
>
> runContextualSearch :: Decomposable g
>                     => ProofProcess g a
>                     -> Either [Wrapped g] a
> runContextualSearch p = fst <$> runStateT (contextualSearch p) []