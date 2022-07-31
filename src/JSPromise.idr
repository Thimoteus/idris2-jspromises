module JSPromise

export
data Promise : Type -> Type where [external]

export
data Rejection : Type where [external]

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

public export
Executor : Type -> Type
Executor a = (a -> IO ()) -> (Rejection -> IO ()) -> IO ()

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

export
ifErr : Rejection -> Bool
ifErr = prim__exists True False . toJsPtr

%foreign "javascript:lambda:k => new Promise(k)"
prim__new : ((JsPtr -> IO ()) -> (Rejection -> IO ()) -> IO ()) -> PrimIO (Promise JsPtr)

export
new : {0 flatten : Flatten a b} -> Executor a -> IO (Promise b)
new = map fromJsPtrP . primIO . prim__new . \k, onPtr => k (onPtr . toJsPtr)

%foreign "javascript:lambda:(k, p) => p.then(k)"
prim__then : (JsPtr -> IO (Promise JsPtr)) -> Promise JsPtr -> PrimIO (Promise JsPtr)

export
then_ : {0 flatten: Flatten b c} -> (a -> IO (Promise b)) -> Promise a -> IO (Promise c)
then_ k pa = fromJsPtrP <$> primIO (prim__then (\ptr => toJsPtrP <$> k (fromJsPtr ptr)) (toJsPtrP pa))

%foreign "javascript:lambda:(k, p) => p.catch(k)"
prim__catch : (Rejection -> IO (Promise JsPtr)) -> Promise JsPtr -> PrimIO (Promise JsPtr)

export
catch : (Rejection -> IO (Promise b)) -> Promise a -> IO (Promise b)
catch k pa = fromJsPtrP <$> primIO (prim__catch (map toJsPtrP . k) (toJsPtrP pa))

%foreign "javascript:lambda:(k, p) => p.finally(k())"
prim__finally : (() -> IO (Promise ())) -> Promise JsPtr -> PrimIO (Promise JsPtr)

export
finally : IO (Promise ()) -> Promise a -> IO (Promise a)
finally mu pa = fromJsPtrP <$> primIO (prim__finally (\_ => mu) (toJsPtrP pa))

%foreign "javascript:lambda:a => Promise.resolve(a)"
prim__resolve : JsPtr -> Promise JsPtr

export
resolve : {0 flatten : Flatten a b} -> a -> Promise b
resolve = fromJsPtrP . prim__resolve . toJsPtr

namespace Lazy
  public export
  data Box a = MkBox a

  public export
  data LazyPromise : Type -> Type where
    MkLazyPromise : IO (Promise (Box a)) -> LazyPromise a

  (>>=) : LazyPromise a -> (a -> LazyPromise b) -> LazyPromise b
  (MkLazyPromise pbioa) >>= k = MkLazyPromise $ do
    pba <- pbioa
    then_ {flatten = FlattenId} (\(MkBox a) => let (MkLazyPromise b) := k a in b) pba

  mutual
    Functor LazyPromise where
      map f pa = do
        a <- pa
        pure (f a)

    Applicative LazyPromise where
      pure = MkLazyPromise . pure . resolve {flatten = FlattenId} . MkBox
      pf <*> pa = do
        f <- pf
        a <- pa
        pure (f a)

    Monad LazyPromise where
      (MkLazyPromise pbioa) >>= k = MkLazyPromise $ do
        pba <- pbioa
        then_ {flatten = FlattenId} (\(MkBox a) => let (MkLazyPromise b) := k a in b) pba
      join pa = pa >>= id

  HasIO LazyPromise where
    liftIO = MkLazyPromise . map (resolve {flatten = FlattenId} . MkBox)
