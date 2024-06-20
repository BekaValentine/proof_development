A free monad approach is also not entirely uncommon, but we'll omit discussion of such a thing here. Instead, I want to jump straight to a free_r_ monad appraoch, and in fact one that is especially extremal in how it applies freer monads. See Kiselyov and Ishii's fantastic paper "Freer Monads, More Extensible Effects" (https://okmij.org/ftp/Haskell/extensible/more.pdf) for an overview of what freer monads are. We merely define them here so that they program will run:

> data Freer i a where
>   Return :: a -> Freer i a
>   Instruction :: i r -> (r -> Freer i a) -> Freer i a
>
> instance Functor (Freer i) where
>   fmap f (Return x) = Return (f x)
>   fmap f (Instruction i k) = Instruction i (fmap f . k)
>
> instance Applicative (Freer i) where
>   pure = Return
>   Return f <*> x = fmap f x
>   Instruction i k <*> x = Instruction i (\v -> k v <*> x)
>
> instance Monad (Freer i) where
>   Return x >>= f = f x
>   Instruction i k >>= f = Instruction i (\v -> k v >>= f)
>
> prove :: i a -> Freer i a
> prove i = Instruction i Return

Now, how do we use this freer monad to implement the Peano proof system? Well, the freer monad _is_ a monad, after all, so the previous monading one will work, but that's sort of missing the point. We want to be extremal in how we use this, to demonstrate a technique. So the way we implement this is by treating the judgments of the proof system as the instructions `i`:

> data PlusI r where
>   Plus :: Nat -> Nat -> PlusI Nat

How then do we make us of this? One answer might be to define an evaluator/executor that directly manages the meanings of the `Plus` instructions/judgements. I'll put that here only for discussion purposes:

> badEvalPlusI :: Freer PlusI a -> a
> badEvalPlusI (Return x) = x
> badEvalPlusI (Instruction (Plus Zero n) k) = badEvalPlusI (k n)
> badEvalPlusI (Instruction (Plus (Suc m) n) k) =
>   badEvalPlusI (Instruction (Plus m n) (\p -> k (Suc p)))

Why do I say this is bad? Well, the meaning of the judgments defined somehow in terms of a big, complex whole process of interpreting programs. We have to explain it by inspecting whole programs, and we're really quite free in how we do that. Fortunately, the freer monad tightly constrains us to which parts of this are actually accessible at any given moment, but we still have access to the continuation part `k` of the freer programs. Indeed, we _must_ have access to it, because we need to explain the meanings in terms of it. But the meaning really.. isn't related to that continuation. We can do better, isolate the meaning components, and make things cleaner.

The way we do this is by introducing a decomposition function which takes a single `PlusI` instruction/judgment, and decomposes it into a freer program:

> {-
> decomposePlusI :: PlusI a -> Freer PlusI a
> decomposePlusI (Plus Zero n) = Return n
> decomposePlusI (Plus (Suc m) n) = Instruction (Plus m n) (\p -> Return (Suc p))
> -}

Actually, let's just use the monadic interface for freer, since at this point it's far cleaner and should be fine for understanding:

> decomposePlusI :: PlusI a -> Freer PlusI a
> decomposePlusI (Plus Zero n) =
>    return n
> decomposePlusI (Plus (Suc m) n) =
>    do p <- instr (Plus m n)
>       return (Suc p)

You'll observe that this decomposing function is _precisely_ what the inference rules do. Each inference rule has a judgment as its conclusion, and zero or more judgments as premises, but as a tool, a rule is used to _decompose_ an as of yet unproven goal judgment into a small piece of proof, together with a collection of _subgoals_. Thus, the decomposition function here likewise explains how to decompose a judgment-as-goal into subgoals.

We now use this decomposition function to define the evaluator:

> evalPlusI :: Freer PlusI a -> a
> evalPlusI (Return x) = x
> evalPlusI (Instruction i k) = evalPlusI (decomposePlusI i >>= k)

In fact, this is such a generic pattern that we can define a type class:

> class Decomposable i where
>   decompose :: i r -> Freer i r
>
> evalFreer :: Decomposable i => Freer i a -> a
> evalFreer (Return x) = x
> evalFreer (Instruction i k) = evalFreer (decompose i >>= k)

We won't make use of this pattern in this tutorial because committing to it at this point is actually burdensome later when we want to talk about the three features of a shallow embedding. We may return to it, tho!

Let's consider now a simple task: logging every problem/goal that the evaluation of a `PlusI` program has to perform:

> logEvalPlusI :: Freer PlusI a -> ([PlusI Nat], a)
> logEvalPlusI (Return x) = ([], x)
> logEvalPlusI (Instruction i@(Plus _ _) k) =
>   let (l, x) = logEvalPlusI (decomposePlusI i >>= k)
>   in (i:l, x)

The pattern match on `i` is simply because the GADT prevents the type checker from seeing that `i` must be of type `PlusI Nat` without it.

Now, this definition for logging is really quite monadic, and we could convert it over to using the `Writer` monad if we wanted and clean it up, but let's not do that just yet. Let's also temporarily put aside the obvious common structure with the basic evaluation function. Let's instead consider how unpleasant it would've been to do this with the mere functional and basic monadic definitions. First and foremost, there is no concrete representation of the goals at all, we have only the functions, and so to record that the goal was `plus M N P`, we need to invent some datatype that records this. Obviously since there's only one judgment, this is easy enough by simply recording a pair of numbers, but when there's two or more judgments we need some new datatype that represents the judgments, so we effectively re-invent `PlusI`. But let's persist, and we'll see what the second issue is:

> loggingPlus1 :: Nat -> Nat -> ([(Nat,Nat)], Nat)
> loggingPlus1 Zero n = ([(Zero,n)], n)
> loggingPlus1 (Suc m) n =
>   let (l,p) = loggingPlus1 m n
>   in  ((Suc m,n):l, p)

The logic of logging here is not in a generic evaluator, but is in the definition of `loggingPlus1` itself. Likewise for the monadic version:

> loggingPlus2 :: Monad m => Nat -> Nat -> m ([(Nat,Nat)], Nat)
> loggingPlus2 Zero n =
>   return ([(Zero,n)], n)
> loggingPlus2 (Suc m) n =
>   do (l,p) <- loggingPlus2 m n
>      return ((Suc m,n):l, Suc p)

Or perhaps if we wanted to use `MonadWriter`:

> loggingPlus3 :: MonadWriter [(Nat,Nat)] m => Nat -> Nat -> m Nat
> loggingPlus3 Zero n =
>   do tell [(Zero,n)]
>      return n
> loggingPlus3 (Suc m) n =
>   do tell [(Suc m, n)]
>      p <- loggingPlus3 m n
>      return (Suc p)

There is now nothing in this implementation of our basic little logic that corresponds to _precisely_ and _only_ the inference rules for the `plus M N P` judgment! We have glued together the functions that represent the meaning of that judgment with the _inessential and application specific_ logging that we wish to do. This is the second problem, and it is gross, gross, gross!

With the freer version of this, the `decomposePlusI` function is completely untouched, the _only_ place that we had to deal with logging was in the evaluator which defered to `decomposePlusI` for the meaning of the judgments.

A third problem is, what happens when we add another judgment? Well, in the freer version, we simply record the judgments and move on. They can all be recorded without anything special happening if we use a simple existential wrapper to hide the return type of each judgment, removing the need for that stray pattern match:

> data Wrapped i where
>   Wrap :: i r -> Wrapped i
>
> logEvalPlusI2 :: Freer PlusI a -> ([Wrapped PlusI], a)
> logEvalPlusI2 (Return x) = ([], x)
> logEvalPlusI2 (Instruction i k) =
>   let (l, x) = logEvalPlusI2 (decomposePlusI i >>= k)
>   in (Wrap i:l, x)

But if we want to do the same thing with the direct functional implementation, or the basic monadic implementation, _each implementing function has to implement the logging separately_. The types will _suggest_ to us that we do the right thing, but they don't guarantee anything at all. We can have a type that looks appropriate and simply forget to log anything. This is _especially_ easy with a `MonadWriter` version, where the absence of logging is simply the omission of the `tell` statements! The other two versions at least forces us to write _something_ for the list of logged judgments, but the silent propagation of the log means that we can silently screw up. Not good at all!

This problem extends to any kind of inspection, not just logging. The use of a concrete representation for judgments/instructions and for proof programs, means that there is some amount of inspection that's possible. But with the basic functional and monadic implementations, there's just no real way to inspect anything because it's all function calls that immediately evaluate in Haskell, rather than having evaluation driven by an explicit function.

Ok, so what about reporting errors? Well, the version with `plus M N P` as the only judgment isn't capable of errors, so let's introduce another kind of judgment: subtraction. In particular, subtraction of strictly smaller numbers, where subtraction of larger numbers is an error. Such a new judgment, call it `minus M N P`, would technically be a different mode assignment to the unmoded `sum M N P` judgment, tho this is a fun fact, more than anything.

Here is the basic functional/monadic version, using a specific choice for representing errors:

> minus1 :: Nat -> Nat -> Maybe Nat
> minus1 m Zero = Just m
> minus1 Zero _ = Nothing
> minus1 (Suc m) (Suc n) = minus1 m n

Alternatively, we could use an `Either` with an error message. That would be more informative:

> data Err
>   = MinusError n -- cannot subtract `n` from 0
> 
> minus2 :: Nat -> Nat -> Either Err Nat
> minus2 m Zero = Right m
> minus2 Zero n = Left (MinusError n)
> minus2 (Suc m) (suc n) = minus2 m n

The implementation of `plus` would have to be augmented to use the `Maybe Nat` or `Either Err Nat` return type. Note that we only have a single error constructor here because only `minus` can fail and only in one way, but obviously we would just have more for each kind of error possible.

Now, how would we do this using a freer monadic approach? Simple: add another judgment/instruction, and simply _return the judgment that can't be proven_!

> data MathI2 r where
>   Plus2 :: Nat -> Nat -> MathI2 Nat
>   Minus2 :: Nat -> Nat -> MathI2 Nat
>
> decomposeMathI2 :: MathI2 a -> Freer MathI2 a
> decomposeMathI2 (Plus Zero n) =
>   return n
> decomposeMathI2 (Plus (Suc m) n) =
>   do p <- instr (Plus m n)
>      return (Suc p)
> decomposeMathI2 (Minus m Zero) =
>   return m
> decomposeMathI2 (Minus Zero n) =
>   
