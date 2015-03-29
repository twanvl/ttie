{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

#define USE_HUGHES_PJ 0

module Util.Pretty
  ( module Util.Pretty
#if USE_HUGHES_PJ
  , module Text.PrettyPrint.HughesPJ
#elif USE_REAL_WL_PPRINT
  , module Text.PrettyPrint.Leijen
#else
  , module Util.WLPPrint
#endif
  ) where

import Prelude ()
import Util.MyPrelude

#if USE_HUGHES_PJ 
import Text.PrettyPrint.HughesPJ hiding ((<>),($$),(<+>),first)
import qualified Text.PrettyPrint.HughesPJ as PP
#elif USE_REAL_WL_PPRINT
import Text.PrettyPrint.Leijen hiding (Pretty,empty,pretty,(<$>),(<$$>),(<>),(</>),(<//>))
import qualified Text.PrettyPrint.Leijen as PP
#else
import Util.WLPPrint hiding (Pretty,empty,pretty,(<$>),(<$$>),(<>))
import qualified Util.WLPPrint as PP
#endif

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

#if USE_HUGHES_PJ
infixr 5 </>,$$
infixr 6 <+>

($$) :: Doc -> Doc -> Doc
($$) = (PP.$+$)

(<+>) :: Doc -> Doc -> Doc
(<+>) = (PP.<+>)

(</>) :: Doc -> Doc -> Doc
x </> y = PP.sep [x,y]

indent :: Int -> Doc -> Doc
indent = nest

align :: Doc -> Doc
align = id

showDoc :: Doc -> String
showDoc = render

#else
instance Monoid Doc where
  mempty = PP.empty
  mappend = (PP.<>)

infixr 5 $$

showDoc :: Doc -> String
showDoc = flip displayS "" . renderPretty 0.8 110

($$) :: Doc -> Doc -> Doc
($$) = (PP.<$>)

($-$) :: Doc -> Doc -> Doc
($-$) = (PP.<$$>)
#endif

--instance Error Doc where
--  noMsg = PP.empty
--  strMsg = text

failDoc :: Monad m => Doc -> m a
failDoc = fail . showDoc

--------------------------------------------------------------------------------
-- Monadic/applicative
--------------------------------------------------------------------------------

(<$$>), (<<>>), (<<+>>), (<$/$>) :: Applicative m => m Doc -> m Doc -> m Doc
(<$$>) = liftA2 ($$)
(<<>>) = liftA2 (<>)
(<<+>>) = liftA2 (<+>)
(<$/$>) = liftA2 ($/$)

textM :: Applicative m => String -> m Doc
textM = pure . text

nestM :: Functor m => Int -> m Doc -> m Doc
nestM n = fmap (nest n)

indentM :: Functor m => Int -> m Doc -> m Doc
indentM n = fmap (indent n)

groupM :: Functor m => m Doc -> m Doc
groupM = fmap group

groupsM :: Applicative m => [m Doc] -> m Doc
groupsM = fmap groups . sequenceA

--------------------------------------------------------------------------------
-- Pretty printing class
--------------------------------------------------------------------------------

-- | Things that can be pretty printed
class Pretty a where
  ppr :: Int -> a -> Doc
  pretty :: a -> String
  pretty = showDoc . ppr 0
  default ppr :: Show a => Int -> a -> Doc
  ppr p x = text (showsPrec p x "")

instance Pretty String where
  ppr _ = text

instance Pretty Doc where
  ppr _ = id

instance Pretty Int where
  ppr _ = text . show

instance Pretty () where
instance Pretty Void where

instance (Pretty a, Pretty b) => Pretty (a,b) where
  ppr _ (x,y) = parens (ppr 0 x <> comma <+> ppr 0 y)

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppr p (Left  x) = parenIf (p>0) $ text "Left " <+> ppr 0 x
  ppr p (Right x) = parenIf (p>0) $ text "Right" <+> ppr 0 x

class Pretty1 f where
  ppr1 :: Pretty a => Int -> f a -> Doc

--------------------------------------------------------------------------------
-- Pretty printing utilities
--------------------------------------------------------------------------------

parenIf :: Bool -> Doc -> Doc
parenIf True  = parens
parenIf False = id

alignIf :: Bool -> Doc -> Doc
alignIf True  = align
alignIf False = id

semiBrackets :: [Doc] -> Doc
semiBrackets = encloseSep lbracket rbracket semi

