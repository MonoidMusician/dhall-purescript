module Dhall.Test.Util where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Array
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (for)
import Effect.Aff (Aff, catchError)
import Node.FS.Aff (readdir, stat)
import Node.FS.Stats (isDirectory, isFile)
import Node.Path (FilePath)

foreign import eqArrayBuffer :: ArrayBuffer -> ArrayBuffer -> Boolean

startsWith :: String -> String -> Boolean
startsWith str pre =
  pre == String.take (String.length pre) str

endsWith :: String -> String -> Boolean
endsWith str post =
  post == String.drop (String.length str - String.length post) str

endingWith :: String -> String -> Maybe String
endingWith str post =
  let { before, after } = String.splitAt (String.length str - String.length post) str
  in if after == post then Just before else Nothing

discover2 :: String -> FilePath -> Aff (Array FilePath)
discover2 suffix dir = do
  mixed <- map ((dir <> "/") <> _) <$> catchError (readdir dir) (pure (pure []))
  dirs <- mixed # Array.filterA \d -> stat d <#> isDirectory
  files0 <- mixed # Array.filterA \f -> stat f <#> isFile
  files <- join <$> for dirs \d -> map ((d <> "/") <> _) <$> readdir d
  pure $ (files0 <|> files) # Array.mapMaybe \file -> file `endingWith` suffix
