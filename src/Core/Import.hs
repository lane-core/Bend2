module Core.Import where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist)
import System.FilePath (takeDirectory, (</>))

import Core.Type
import Core.Parse.Book (doParseBook)
import Core.Bind (bindBook)

-- Auto-import unbound references in a Book
autoImport :: FilePath -> Book -> IO Book
autoImport basePath book = do
  let unboundRefs = collectUnboundRefs book
  autoImportRefs basePath book unboundRefs S.empty

-- Collect all unbound references from a Book
collectUnboundRefs :: Book -> S.Set Name
collectUnboundRefs (Book defs) = S.unions $ map collectRefsFromDefn (M.elems defs) where
  collectRefsFromDefn (_, term, typ) = S.union (collectRefs term) (collectRefs typ)

-- Collect all Ref terms from a Term
collectRefs :: Term -> S.Set Name
collectRefs term = case term of
  Ref name    -> S.singleton name
  Var _ _     -> S.empty
  Sub t       -> collectRefs t
  Fix _ f     -> collectRefs (f (Var "dummy" 0))
  Let v f     -> S.union (collectRefs v) (collectRefs f)
  Set         -> S.empty
  Ann x t     -> S.union (collectRefs x) (collectRefs t)
  Chk x t     -> S.union (collectRefs x) (collectRefs t)
  Emp         -> S.empty
  Efq         -> S.empty
  Uni         -> S.empty
  One         -> S.empty
  Use f       -> collectRefs f
  Bit         -> S.empty
  Bt0         -> S.empty
  Bt1         -> S.empty
  Bif f t     -> S.union (collectRefs f) (collectRefs t)
  Nat         -> S.empty
  Zer         -> S.empty
  Suc n       -> collectRefs n
  Swi z s     -> S.union (collectRefs z) (collectRefs s)
  Lst t       -> collectRefs t
  Nil         -> S.empty
  Con h t     -> S.union (collectRefs h) (collectRefs t)
  Mat n c     -> S.union (collectRefs n) (collectRefs c)
  Enu _       -> S.empty
  Sym _       -> S.empty
  Cse cases   -> S.unions (map (collectRefs . snd) cases)
  Sig a b     -> S.union (collectRefs a) (collectRefs b)
  Tup a b     -> S.union (collectRefs a) (collectRefs b)
  Get f       -> collectRefs f
  All a b     -> S.union (collectRefs a) (collectRefs b)
  Lam _ f     -> collectRefs (f (Var "dummy" 0))
  App f x     -> S.union (collectRefs f) (collectRefs x)
  Eql t a b   -> S.unions [collectRefs t, collectRefs a, collectRefs b]
  Rfl         -> S.empty
  Rwt f       -> collectRefs f
  Met _ t ctx -> S.unions (collectRefs t : map collectRefs ctx)
  Ind t       -> collectRefs t
  Frz t       -> collectRefs t
  Loc _ t     -> collectRefs t
  Era         -> S.empty
  Sup _ a b   -> S.union (collectRefs a) (collectRefs b)
  Pat s m c   -> S.unions $ map collectRefs s ++ map (collectRefs . snd) m ++ concatMap (\ (p, b) -> collectRefs b : map collectRefs p) c

-- Auto-import references with cycle detection
autoImportRefs :: FilePath -> Book -> S.Set Name -> S.Set FilePath -> IO Book
autoImportRefs _ book refs _ | S.null refs = return book
autoImportRefs basePath book refs visited = do
  (book', newRefs) <- foldM (autoImportRef basePath visited) (book, S.empty) (S.toList refs)
  if S.null newRefs
    then return book'
    else autoImportRefs basePath book' newRefs visited

-- Auto-import a single reference
autoImportRef :: FilePath -> S.Set FilePath -> (Book, S.Set Name) -> Name -> IO (Book, S.Set Name)
autoImportRef basePath visited (book@(Book defs), newRefs) refName = do
  -- Check if the reference already exists in the book
  if M.member refName defs
    then return (book, newRefs)
    else do
      let filePath = basePath </> (refName ++ ".bend")
      fileExists <- doesFileExist filePath
      if fileExists && not (filePath `S.member` visited)
        then do
          content <- readFile filePath
          case doParseBook filePath content of
            Left err -> do
              putStrLn $ "Warning: Failed to parse " ++ filePath ++ ": " ++ err
              return (book, newRefs)
            Right importedBook -> do
              -- Recursively auto-import the imported book
              let visited' = S.insert filePath visited
              importedBook' <- autoImportRefs (takeDirectory filePath) importedBook 
                                             (collectUnboundRefs importedBook) visited'
              -- Merge the imported book into the current book
              let mergedBook = mergeBooks book importedBook'
              let additionalRefs = collectUnboundRefs importedBook'
              return (mergedBook, S.union newRefs additionalRefs)
        else
          return (book, newRefs)

-- Merge two books, preferring definitions from the first book
mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1) (Book defs2) = Book (M.union defs1 defs2)
