module ApplicativeMonad

||| Create a Functor using >>= and pure
||| Ideally this would take `Monad` as an constraint/auto implicit argument,
||| but Monad requires Applicative first so that unfortunately doesn't work.
monadToFunctor :
    (pure : forall a. a -> f a) ->
    (bind : forall a, b. f a -> (a -> f b) -> f b) ->
    Functor f
monadToFunctor pure bind =
    let map : forall a, b. (a -> b) -> (f a -> f b)
        map f mx = mx `bind` \x => pure (f x)
     in MkFunctor map

||| Create an applicative using bind (>>=) and pure.
monadToApplicative :
    Functor f =>
    (pure : forall a. a -> f a) ->
    (bind : forall a, b. f a -> (a -> f b) -> f b) ->
    Applicative f
monadToApplicative pure bind =
    let app : forall a, b. f (a -> b) -> f a -> f b
        app mf mx =
            mf `bind` \f => map f mx
     in MkApplicative pure app

-- %hint
functorList : Functor List
functorList = monadToFunctor pure (>>=)

-- %hint
applicativeList : Applicative List
applicativeList = monadToApplicative pure (>>=)
