module JSPromise

||| The type of JS promises parameterized by the value they return.
export
data Promise : Type -> Type where [external]
%name Promise pa, pb, pc, p

||| The error type of a promise. Use `ifErr` to check if it exists.
export
data Rejection : Type where [external]

||| Data type used to handle promise semantics that disallow types of Promise (Promise a) to exist.
public export
data Flatten : Type -> Type -> Type where
  FlattenId : Flatten a a
  FlattenPromise : Flatten a b -> Flatten (Promise a) b

data JsPtr : Type where [external]

toJsPtr : a -> JsPtr
toJsPtr = believe_me

fromJsPtr : JsPtr -> a
fromJsPtr = believe_me

toJsPtrP : Promise a -> Promise JsPtr
toJsPtrP = believe_me

fromJsPtrP : Promise JsPtr -> Promise a
fromJsPtrP = believe_me

||| Used to create a new promise given success and error callbacks.
public export
Executor : Type -> Type
Executor a = (a -> IO ()) -> (Rejection -> IO ()) -> IO ()

toPrimIOFn : (c -> a) -> (a -> IO (Promise b)) -> (c -> PrimIO (Promise JsPtr))
toPrimIOFn f k ptr = toPrim $ toJsPtrP <$> k (f ptr)

fromPrimIOFn : (a -> c) -> (c -> PrimIO ()) -> (a -> IO ())
fromPrimIOFn f k x = primIO $ k (f x)

%foreign """
javascript:lambda:(t, f, x) => {
  if (x) {
    return t;
  } else {
    return f;
  }
}
"""
prim__exists : Bool -> Bool -> JsPtr -> Bool

||| Used to check whether a Rejection exists.
export
ifErr : Rejection -> Bool
ifErr = prim__exists True False . toJsPtr

%foreign "javascript:lambda:k => new Promise((s, e) => k(s, e)())"
prim__new : ((JsPtr -> PrimIO ()) -> (Rejection -> PrimIO ()) -> PrimIO ()) -> PrimIO (Promise JsPtr)

export
new : {auto 0 flatten : Flatten a b} -> Executor a -> IO (Promise b)
new f =
  map fromJsPtrP $ primIO $ prim__new $ \onSucc, onErr => toPrim (f (fromPrimIOFn toJsPtr onSucc) (fromPrimIOFn id onErr))

%foreign """
javascript:lambda:(k, p) => p.then((x) => k(x)())
"""
prim__then : (JsPtr -> PrimIO (Promise JsPtr)) -> Promise JsPtr -> PrimIO (Promise JsPtr)

||| Used to chain promises together, similar to the bind operator (>>=).
export
then_ : {auto 0 flatten: Flatten b c} -> (a -> IO (Promise b)) -> Promise a -> IO (Promise c)
then_ f pa =
  map fromJsPtrP $ primIO $ prim__then (toPrimIOFn fromJsPtr f) (toJsPtrP pa)

%foreign "javascript:lambda:(k, p) => p.catch(e => k(e)())"
prim__catch : (Rejection -> PrimIO (Promise JsPtr)) -> Promise JsPtr -> PrimIO (Promise JsPtr)

||| Handle a Rejection to make sure it doesn't throw.
export
catch : (Rejection -> IO (Promise b)) -> Promise a -> IO (Promise b)
catch f pa = do
  map fromJsPtrP $ primIO $ prim__catch (toPrimIOFn id f) (toJsPtrP pa)

%foreign "javascript:lambda:(k, c, p) => p.then(x => k(x)(), e => c(e)())"
prim__thenOrCatch : (JsPtr -> PrimIO (Promise JsPtr)) -> (Rejection -> PrimIO (Promise JsPtr)) -> Promise JsPtr -> PrimIO (Promise JsPtr)

export
thenOrCatch : {auto 0 flatten: Flatten b c} -> (a -> IO (Promise b)) -> (Rejection -> IO (Promise b)) -> Promise a -> IO (Promise c)
thenOrCatch f g pa = map fromJsPtrP $ primIO $ prim__thenOrCatch (toPrimIOFn fromJsPtr f) (toPrimIOFn id g) (toJsPtrP pa)

%foreign "javascript:lambda:(k, p) => p.finally(k)"
prim__finally : (PrimIO (Promise ())) -> Promise JsPtr -> PrimIO (Promise JsPtr)

export
finally : IO (Promise ()) -> Promise a -> IO (Promise a)
finally x pa = map fromJsPtrP $ primIO $ prim__finally (toPrim x) (toJsPtrP pa)

%foreign "javascript:lambda:(a) => Promise.resolve(a)"
prim__resolve : JsPtr -> Promise JsPtr

export
resolve : {auto 0 flatten : Flatten a b} -> a -> Promise b
resolve = fromJsPtrP . prim__resolve . toJsPtr

namespace Lazy
  public export
  data Box a = MkBox a

  export
  unbox : Box a -> a
  unbox (MkBox x) = x

  public export
  data LazyPromise : Type -> Type where
    MkLazyPromise : IO (Promise (Box a)) -> LazyPromise a

  %name LazyPromise pa, pb, pc, p

  mutual
    export
    Functor LazyPromise where
      map f pa = do
        a <- pa
        pure (f a)

    export
    Applicative LazyPromise where
      pure = MkLazyPromise . pure . resolve . MkBox
      pf <*> pa = do
        f <- pf
        a <- pa
        pure (f a)

    export
    Monad LazyPromise where
      (MkLazyPromise pbioa) >>= k = MkLazyPromise $ do
        pba <- pbioa
        then_ (\(MkBox a) => let (MkLazyPromise b) := k a in b) pba

  export
  HasIO LazyPromise where
    liftIO = MkLazyPromise . map (resolve . MkBox)

  export
  new : Executor a -> LazyPromise a
  new k = MkLazyPromise $ JSPromise.new $ \onSucc, onErr => k (onSucc . MkBox) onErr

  export
  catch : (Rejection -> LazyPromise b) -> LazyPromise a -> LazyPromise b
  catch onErr (MkLazyPromise pa) =
    MkLazyPromise $ do
      a <- pa
      JSPromise.catch (\err => let (MkLazyPromise pb) := onErr err in pb) a

  export
  finally : LazyPromise () -> LazyPromise a -> LazyPromise a
  finally (MkLazyPromise pu) (MkLazyPromise pa) =
    MkLazyPromise $ do
      a <- pa
      JSPromise.finally finalize a
    where
      finalize : IO (Promise ())
      finalize = do
        u <- pu
        JSPromise.then_ {flatten = FlattenId} (\(MkBox unit) => pure (JSPromise.resolve unit)) u

  export
  fromPromise : IO (Promise a) -> LazyPromise a
  fromPromise p =
    MkLazyPromise $ then_ {flatten = FlattenId} (pure . resolve . MkBox) =<< p

  export
  toPromise : {auto 0 flatten : Flatten a b} -> LazyPromise a -> IO (Promise b)
  toPromise {flatten} (MkLazyPromise lpa) =
    then_ {flatten = flatten} (\(MkBox b) => pure (resolve b)) =<< lpa

  export
  run : LazyPromise a -> IO (Promise (Box a))
  run (MkLazyPromise x) = x
