module Main

import JSPromise

myProm : Promise Int
myProm = resolve {flatten = FlattenId} 5

promUnit : Promise ()
promUnit = resolve {flatten = FlattenId} ()

myPromProg : IO (Promise ())
myPromProg = then_ {flatten = FlattenId} go myProm
  where
    go : Int -> IO (Promise ())
    go n = do
      putStrLn $ show n
      pure promUnit

main : IO ()
main = do
  putStrLn "Hi!"
