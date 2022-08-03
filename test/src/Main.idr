module Main

import JSPromise

data Array : Type -> Type where [external]
%name Array xs, ys, zs

%foreign """
javascript:lambda:(_, xs, k) => {
  for (const x of xs) {
    k(x)();
  }
}
"""
prim__arrayFor : Array a -> (a -> PrimIO()) -> PrimIO ()

arrayFor_: Array a -> (a -> IO ()) -> IO ()
arrayFor_ xs f = primIO (prim__arrayFor xs (\x => toPrim (f x)))

%foreign "javascript:lambda:(str) => require('node:fs/promises').readdir(str)"
prim__readdir : String -> PrimIO (Promise (Array String))

readdir : String -> IO (Promise (Array String))
readdir str = primIO (prim__readdir str)

readdirL : String -> LazyPromise (Array String)
readdirL str = fromPromise (readdir str)

myPromProgL : LazyPromise ()
myPromProgL = do
  pfs <- readdirL "./"
  liftIO $ putStr "reading complete"
  liftIO $ arrayFor_ pfs $ \file => putStr file

myPromProg : IO (Promise ())
myPromProg = then_ {flatten = FlattenId} k x
  where
    k : String -> IO (Promise ())
    k y = do
      putStr $ y ++ " = five"
      pure $ resolve ()
    x : Promise String
    x = resolve "5"

noProms : LazyPromise ()
noProms = do
  putStrLn "Hello"
  putStrLn "I am"
  putStrLn "printing"

main : IO ()
main = do
  ignore $ run $ do
    noProms
    myPromProgL
  _ <- myPromProg
  pure ()
