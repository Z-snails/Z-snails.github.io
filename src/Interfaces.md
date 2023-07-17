# Interface Desugaring

<!-- idris
module Interfaces
-->

If you've done enough Idris, you've surely heard that interfaces are just records with syntax sugar. But what is that syntax sugar, and why should you care? Most of the time you shouldn't care, but there are some very useful techniques you can use if you scrap some of the sugar.

First of all I'll define some terms:
implicit argument
: an argument which Idris fills in using various techniques. Usually this is done by checking the types of the arguments and expected return type to try and uniquely determine the value - this is how generics in Idris work. These can be written as `{0 a : Type} -> ...`, `{len : Nat} -> ...` or `forall x. ...`.

auto implicit argument
: This is a type of implicit arg which Idris fills in using proof search, ie Idris uses provided definitions, interface implementations and local variables to try and fill in the argument. These can be written as `{auto _ : x === y} -> ...` or `Functor f =>`.

default implicit argument
: When writing the function, you can provide a default value for the argument, which will be used unless it is overwriten at the call site. These are written as `{default False pretty : Bool} -> ...`

Let's take the following interface and manually desugar it one step at a time. As we go I'll explain when this might be useful.

```idris
interface Interface a where
    constructor MkInterface
    getLength : a -> Nat
    getTail : a -> Maybe a

namespace InterfaceList
    implementation Interface (List a) where
        getLength xs = length xs

        getTail [] = Nothing
        getTail (_ :: xs) = Just xs
```

The `constructor` declaration in the interface works the same way as in a record - it isn't generally needed to use interfaces, but it helps when manually constructing an interface. I put the implementation in it's own namespace, so that it doesn't interfere with the implementation below - proof search has to come up with a single solution, otherwise Idris throws an error.

Let's start by manually desugaring the `implementation`.

```idris
%hint
interfaceListImpl : Interface (List a)
interfaceListImpl = MkInterface
    { getLength = getLengthImpl
    , getTail = getTailImpl
    }
  where
    getLengthImpl : List a -> Nat
    getTailImpl : List a -> Maybe (List a)

    getLengthImpl xs = length xs

    getTailImpl [] = Nothing
    getTailImpl (_ :: xs) = Just xs
```

`%hint` tells Idris to use this name when trying to search for an implementation of `Interface (List a)`. I will explain how later. Now just doing this isn't especially useful - you might as well just write a regular `implementation`, but it can be helpful when you *don't* add `%hint`, as this allows you to write multiple named implementations, or a default implementation and alternative ones. This is so useful in fact that Idris has more syntax sugar for this: named implementations.

```idris
[Sum] Semigroup Nat where
    x <+> y = x + y

[Product] Semigroup Nat where
    x <+> y = x * y
```

As `Nat` has (at least) 2 sensible and valid `Semigroup` implementations, it makes sense to define them both, and allow other programmers to pick which one to use; these implementations are part of Idris's prelude.

Another possible use case is writing helper functions to simplify writing implementations, which is often done when implementing `Applicative` and `Monad`. I show one way to do this in [ApplicativeMonad.idr](./ApplicativeMonad.idr)

Now to the interface itself:

```idris
%prefix_record_projections off

record Interface' a where
    constructor MkInterface'
    getLength : a -> Nat
    getTail : a -> Maybe a
```

Due to `%prefix_record_projections off`, Idris does not generate a `getLength` function, only a `.getLength` one - these are 2 seperate names, which is helpful for us, but Idris doesn't ever generate the postfix projections (`.getLength`) when desugaring an interface.

```idris
getLength' : Interface' a => a -> Nat
getLength' @{impl} = impl.getLength

getTail' : Interface' a => a -> Maybe a
getTail' @{impl} = impl.getTail
```

`@{ }` allows you to name or pattern match on an auto implicit argument, which I use here to name the `Interace'` implementation in order to use record projections to extract the functions I need. This can also be used when calling a function to specifiy an auto implicit argument.

Let's also have a quick look at calling a function from an interface.

```idris
shorten : List a -> List a
shorten xs = if getLength xs > 10
    then case getTail xs of
        Just tail => shorten tail
        Nothing => xs
    else xs
```

For the `getLength` and `getTail` calls, Idris has to find an implementation for `Interface (List a)`. Idris does this by maintaining a list of all the `%hint`ed definitions (including `implementation`s) and when it comes across auto implicit argument, or `%search` it checks through them for any that have the correct return type. If the `%hint`ed definition has additional auto implicit arguments Idris recursively searches for those too, such as in `Show a => Show (List a)` - when trying to find an implementation of `Show (List a)`, Idris will find this hint and then search for an implementation of `Show a`. Here Idris will find `interfaceListImpl`, which we added `%hint` to earlier, and use that as the auto implicit argument to `getLength` and `getTail`.

One more thing we to cover is interface sub-typing, ie using an implementation of say `Applicative` to use the `map` function, as every `Applicative` is also a `Functor`.

```idris
-- I for interface
interface FunctorI f where
    constructor MkFunctorI
    mapI : (a -> b) -> (f a -> f b)

interface FunctorI f => ApplicativeI f where
    constructor MkApplicativeI
    pure' : a -> f a
    (<**>) : f (a -> b) -> f a -> f b
```

`Functor'` is desugared to a record exactly the same way as `Interface` from earlier, but `Applicative'` is a little different, due to the `Functor'` constraint.

```idris
-- R for record
record FunctorR f where
    constructor MkFunctorR
    mapR : (a -> b) -> (f a -> f b)

record ApplicativeR f where
    constructor MkApplicativeR
    {auto functor : FunctorR f}
    pureR : a -> f a
    apR : f (a -> b) -> f a -> f b
    -- ap is the usual name for the <*> operator
```

The `functor` field allows Idris to get an implementation of `FunctorR` from an implementation of `ApplicativeR`. In an actual `interface` Idris gives this a unique name, which is not possible to input - these are called machine names. 

```
:s Applicative f -> Functor f
Prelude.Interfaces.Constraint (Functor f) : Applicative f -> Functor f
```

`Constraint (Functor f)` isn't the actual machine name; it's a display name, which helps the programmer understand, as machine names aren't very helpful or readable.
