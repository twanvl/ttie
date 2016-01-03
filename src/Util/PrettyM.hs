{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Util.PrettyM
  ( module Util.PrettyM
  , Doc
  ) where

import Prelude ()
import Util.MyPrelude

import Util.WLPPrint (Doc)
import qualified Util.WLPPrint as PP

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

instance Monoid Doc where
  mempty = PP.empty
  mappend = (PP.<>)

infixr 4 $$,$-$
infixl 5 $/$
infixr 6 <.>,<+>

showDoc :: Doc -> String
showDoc = flip PP.displayS "" . PP.renderPretty 0.9 120

showsDoc :: Doc -> ShowS
showsDoc = showString . showDoc

($$),(<.>),(<+>),($/$),($-$) :: Applicative m => m Doc -> m Doc -> m Doc
($$) = liftA2 (PP.$$)
(<.>) = liftA2 (PP.<>)
(<+>) = liftA2 (PP.<+>)
($/$) = liftA2 (PP.$/$)
($-$) = liftA2 (PP.<$$>)

--------------------------------------------------------------------------------
-- Monadic/applicative wrappers
--------------------------------------------------------------------------------

emptyDoc :: Applicative m => m Doc
emptyDoc = pure PP.empty

text :: Applicative m => String -> m Doc
text = pure . PP.text

int :: Applicative m => Int -> m Doc
int = pure . PP.int

nest :: Functor m => Int -> m Doc -> m Doc
nest n = fmap (PP.nest n)

indent :: Functor m => Int -> m Doc -> m Doc
indent n = fmap (PP.indent n)

group, align, flatten, parens, angles, braces, brackets :: Functor m => m Doc -> m Doc
group  = fmap PP.group
align  = fmap PP.align
flatten = fmap PP.flatten
parens = fmap PP.parens
angles = fmap PP.angles
braces = fmap PP.braces
brackets = fmap PP.brackets

groups, hsep, hcat, vcat :: Applicative m => [m Doc] -> m Doc
groups = fmap PP.groups . sequenceA
hsep = fmap PP.hsep . sequenceA
hcat = fmap PP.hcat . sequenceA
vcat = fmap PP.vcat . sequenceA

encloseSep :: Applicative m => m Doc -> m Doc -> m Doc -> [m Doc] -> m Doc
encloseSep a b c d = PP.encloseSep <$> a <*> b <*> c <*> sequenceA d

lbracket, rbracket, lparen, rparen, lbrace, rbrace, comma, semi :: Applicative m => m Doc
lbracket = pure PP.lbracket
rbracket = pure PP.rbracket
lparen   = pure PP.lparen
rparen   = pure PP.rparen
lbrace   = pure PP.lbrace
rbrace   = pure PP.rbrace
comma    = pure PP.comma
semi     = pure PP.semi

--------------------------------------------------------------------------------
-- Pretty printing class
--------------------------------------------------------------------------------

-- | Things that can be pretty printed
class Applicative m => Pretty m a where
  ppr :: Int -> a -> m Doc
  default ppr :: Show a => Int -> a -> m Doc
  ppr p x = text (showsPrec p x "")

ppr' :: Pretty Identity a => a -> Doc
ppr' = runIdentity . ppr 0

pretty :: Pretty Identity a => a -> String
pretty = showDoc . ppr'

instance Applicative m => Pretty m String where
  ppr _ = text

instance Applicative m => Pretty m Doc where
  ppr _ = pure

instance Applicative m => Pretty m Int where
  ppr _ = int

instance Applicative m => Pretty m () where
instance Applicative m => Pretty m Void where
instance Applicative m => Pretty m Bool where

instance (Pretty m a, Pretty m b) => Pretty m (a,b) where
  ppr _ (x,y) = parens (ppr 0 x <.> comma <+> ppr 0 y)

instance (Pretty m a, Pretty m b, Pretty m c) => Pretty m (a,b,c) where
  ppr _ (x,y,z) = parens (ppr 0 x <.> comma <+> ppr 0 y <.> comma <+> ppr 0 z)
  
instance (Pretty m a, Pretty m b) => Pretty m (Either a b) where
  ppr p (Left  x) = parenIf (p>0) $ text "Left " <+> ppr 0 x
  ppr p (Right x) = parenIf (p>0) $ text "Right" <+> ppr 0 x

class Pretty1 m f where
  ppr1 :: Pretty m a => Int -> f a -> m Doc

--------------------------------------------------------------------------------
-- Pretty printing utilities
--------------------------------------------------------------------------------

parenIf :: Functor m => Bool -> m Doc -> m Doc
parenIf True  = parens
parenIf False = id

alignIf :: Functor m => Bool -> m Doc -> m Doc
alignIf True  = align
alignIf False = id

parenAlignIf :: Functor m => Bool -> m Doc -> m Doc
parenAlignIf True  = parens . align
parenAlignIf False = id

semiBrackets, semiBraces, commaBrackets :: Applicative m => [m Doc] -> m Doc
semiBrackets  = encloseSep lbracket rbracket semi
semiBraces    = encloseSep lbrace   rbrace   semi
commaBrackets = encloseSep lbracket rbracket comma

