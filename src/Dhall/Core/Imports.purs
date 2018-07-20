module Dhall.Core.Imports where

import Prelude

import Data.Foldable (foldMap)
import Data.List (List)
import Data.Maybe (Maybe(..))

-- | Internal representation of a directory that stores the path components in
-- | reverse order
-- | In other words, the directory `/foo/bar/baz` is encoded as
-- | `Directory { components = [ "baz", "bar", "foo" ] }`
newtype Directory = Directory (List String)
derive instance eqDirectory :: Eq Directory
derive instance ordDirectory :: Ord Directory

instance semigroupDirectory :: Semigroup Directory where
  append (Directory components₀) (Directory components₁) =
    Directory (components₁ <> components₀)
instance monoidDirectory :: Monoid Directory where
  mempty = Directory mempty

prettyDirectory :: Directory -> String
prettyDirectory (Directory components) = foldMap ("/" <> _) components

-- | A `File` is a `directory` followed by one additional path component
-- | representing the `file` name
newtype File = File { directory :: Directory, file :: String }
derive instance eqFile :: Eq File
derive instance ordFile :: Ord File
instance semigroupFile :: Semigroup File where
  append (File f1) (File f2) = File
    { directory: f1.directory <> f2.directory
    , file: f2.file
    }

prettyFile :: File -> String
prettyFile (File { directory, file }) = prettyDirectory directory <> "/" <> file

data FilePrefix
  = Absolute -- Absolute path
  | Here -- Path relative to `.`
  | Home -- Path relative to `~`

derive instance eqFilePrefix :: Eq FilePrefix
derive instance ordFilePrefix :: Ord FilePrefix

prettyFilePrefix :: FilePrefix -> String
prettyFilePrefix Absolute = ""
prettyFilePrefix Here = "."
prettyFilePrefix Home = "~"

-- | The type of import (i.e. local vs. remote vs. environment)
data ImportType
  -- Local path
  = Local FilePrefix File
  -- URL of remote resource and optional headers stored in an import
  | URL String File String (Maybe ImportHashed)
  -- Environment variable
  | Env String
  | Missing

derive instance eqImportType :: Eq ImportType
derive instance ordImportType :: Ord ImportType

instance semigroupImportType :: Semigroup ImportType where
  append (Local prefix file₀) (Local Here file₁) =
    Local prefix (file₀ <> file₁)

  append (URL prefix file₀ suffix headers) (Local Here file₁) =
    URL prefix (file₀ <> file₁) suffix headers

  append _ import₁ =
    import₁

prettyImportType :: ImportType -> String
prettyImportType (Local prefix file) =
  prettyFilePrefix prefix <> prettyFile file
prettyImportType (URL prefix file suffix headers) =
      prefix
  <>  prettyFile file
  <>  suffix
  <>  foldMap prettyHeaders headers
  where
    prettyHeaders h = " using " <> prettyImportHashed h
prettyImportType (Env env) = "env:" <> show env
prettyImportType Missing = "missing"

-- | How to interpret the import's contents (i.e. as Dhall code or raw text)
data ImportMode = Code | RawText

derive instance eqImportMode :: Eq ImportMode
derive instance ordImportMode :: Ord ImportMode

-- | A `ImportType` extended with an optional hash for semantic integrity checks
newtype ImportHashed = ImportHashed
  { hash       :: Maybe String
  , importType :: ImportType
  }

derive instance eqImportHashed :: Eq ImportHashed
derive instance ordImportHashed :: Ord ImportHashed

instance semigroupImportHashed :: Semigroup ImportHashed where
  append (ImportHashed ih0) (ImportHashed ih1) = ImportHashed
    { hash: ih1.hash, importType: ih0.importType <> ih1.importType }

prettyImportHashed :: ImportHashed -> String
prettyImportHashed (ImportHashed { hash: Nothing, importType: p }) =
  prettyImportType p
prettyImportHashed (ImportHashed { hash: Just h, importType: p }) =
  prettyImportType p <> " sha256:" <> h

-- | Reference to an external resource
newtype Import = Import
  { importHashed :: ImportHashed
  , importMode   :: ImportMode
  }

instance semigroupImport :: Semigroup Import where
  append (Import i0) (Import i1) = Import
    { importHashed: i0.importHashed <> i1.importHashed
    , importMode: i1.importMode
    }

prettyImport :: Import -> String
prettyImport (Import { importHashed, importMode }) =
  prettyImportHashed importHashed <> suffix
      where
        suffix :: String
        suffix = case importMode of
            RawText -> " as Text"
            Code    -> ""
