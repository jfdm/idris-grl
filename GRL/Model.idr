 module GRL.Model

import public Data.AVL.Set
import public Data.List

import public GRL.Common

%access public
-- ---------------------------------------------------------- [ ADT Definition ]
data GModel : ElemTy -> Type where
  -- Model Instance
  GRLSpec : List (GModel ELEM)
          -> List (GModel ILINK)
          -> List (GModel SLINK)
          -> GModel MODEL
  -- Elements
  ||| A (hard) Goal is a condition or state of affairs in the
  ||| world that the stakeholders would like to achieve.
  |||
  ||| How the goal is to be achieved is not specified, allowing
  ||| alternatives to be considered. A goal can be either a business
  ||| goal or a system goal. A business goal expresses goals regarding
  ||| the business or state of the business affairs the individual or
  ||| organization wishes to achieve. A system goal expresses goals
  ||| the target system should achieve and generally describes the
  ||| functional requirements of the target information system.
  Goal : String -> Maybe EvalVal -> Maybe DecompTy -> GModel ELEM
  ||| Softgoals are often used to describe qualities and
  ||| non-functional aspects such as security, robustness,
  ||| performance, usability, etc.
  |||
  ||| A Softgoal is a condition or state of affairs in the world that
  ||| the actor would like to achieve, but unlike in the concept of
  ||| (hard) goal, there are no clear-cut criteria for whether the
  ||| condition is achieved, and it is up to subjective judgement and
  ||| interpretation of the modeller to judge whether a particular
  ||| state of affairs in fact achieves sufficiently the stated
  ||| softgoal.
  Soft : String -> Maybe EvalVal -> Maybe DecompTy -> GModel ELEM
  ||| a Task specifies a particular way of doing something.
  |||
  ||| When a task is part of the decomposition of a (higher-level)
  ||| task, this restricts the higher-level task to that particular
  ||| course of action. Tasks can also be seen as the solutions in the
  ||| target system, which will address (or operationalize) goals and
  ||| softgoals. These solutions provide operations, processes, data
  ||| representations, structuring, constraints and agents in the
  ||| target system to meet the needs stated in the goals and
  ||| softgoals.
  Task : String -> Maybe EvalVal -> Maybe DecompTy -> GModel ELEM

  ||| A Resource is a physical or informational entity, for which the
  ||| main concern is whether it is available.
  Res  : String -> Maybe EvalVal -> Maybe DecompTy -> GModel ELEM

  -- Intentional

  ||| A Contribution defines the level of impact that the
  ||| satisfaction of a source intentional element or indicator has on
  ||| the satisfaction of a destination intentional element.
  Impacts : Contrib -> GModel ELEM -> GModel ELEM -> GModel ILINK

  |||  A correlation link emphasizes side-effects between intentional
  ||| elements in different categories or actor definitions.
  Effects : Contrib -> GModel ELEM -> GModel ELEM -> GModel ILINK
  -- Structure

  ||| The AND Decomposition link enables the hierarchical
  ||| decomposition of a target intentional element by a source
  ||| element. A target intentional element can be decomposed into
  ||| many source intentional elements using as many decomposition
  ||| links. All of the source intentional elements are necessary for
  ||| the target intentional element to be satisfied.
  AND : GModel ELEM -> List (GModel ELEM) -> GModel SLINK

  ||| The XOR Decomposition link enables the description of
  ||| alternative means of satisfying a target intentional element:
  ||| Mutually exclusive. The satisfaction of one and only one of the
  ||| sub-intentional elements is necessary to achieve the target.
  XOR : GModel ELEM -> List (GModel ELEM) -> GModel SLINK

  ||| The IOR Decomposition link enables the description of
  ||| alternative means of satisfying a target intentional element:
  ||| Not mutually exclusive. The satisfaction of one of the
  ||| sub-intentional elements is sufficient to achieve the target,
  ||| but many sub-intentional elements can be satisfied.
  IOR : GModel ELEM -> List (GModel ELEM) -> GModel SLINK

-- ---------------------------------------------------- [ Allowed Constructors ]
emptyModel : GModel MODEL
emptyModel = GRLSpec Nil Nil Nil

goal : String -> Maybe EvalVal -> GModel ELEM
goal s e = Goal s e Nothing

soft : String -> Maybe EvalVal -> GModel ELEM
soft s e = Soft s e Nothing

task : String -> Maybe EvalVal -> GModel ELEM
task s e = Task s e Nothing

resource : String -> Maybe EvalVal -> GModel ELEM
resource s e = Res s e Nothing

impacts : Contrib -> GModel ELEM -> GModel ELEM -> GModel ILINK
impacts c a b = Impacts c a b

effects : Contrib -> GModel ELEM -> GModel ELEM -> GModel ILINK
effects c a b = Effects c a b

and : GModel ELEM -> List (GModel ELEM) -> GModel SLINK
and a bs = AND a bs

xor : GModel ELEM -> List (GModel ELEM) -> GModel SLINK
xor a bs = XOR a bs

ior : GModel ELEM -> List (GModel ELEM) -> GModel SLINK
ior a bs = IOR a bs

-- ----------------------------------------------------------- [ Show Instance ]

instance Show (GModel ty) where
  show (GRLSpec es ls is) = unwords ["[Model ", show es, show ls, show is, "]\n"]
  show (Goal t v d)      = unwords ["[Goal ", show t, show v, show d, "]"]
  show (Task t v d)      = unwords ["[Task ", show t, show v, show d, "]"]
  show (Soft t v d)      = unwords ["[Soft ", show t, show v, show d, "]"]
  show (Res t v d)       = unwords ["[Res ", show t, show v,  show d, "]"]

  show (Impacts c a b) = unwords ["[Impacts ", show a, show c, show b, "]\n"]
  show (Effects c a b) = unwords ["[Effects ", show a, show c, show b, "]\n"]

  show (AND e es) = unwords ["[", show e, "&&", show es, "]"]
  show (XOR e es) = unwords ["[", show e, "XOR", show es, "]"]
  show (IOR e es) = unwords ["[", show e, "||", show es, "]"]

-- ---------------------------------------------------------------------- [ Eq ]

-- @TODO Make total.
mutual
  %assert_total
  gModelEq : (GModel x) -> (GModel y) -> Bool
  gModelEq (GRLSpec (x::xes) (x'::xls) (x''::xis)) (GRLSpec (y::yes) (y'::yls) (y''::yis)) =
    gModelEq x y     && xes == yes &&
    gModelEq x' y'   && xls == yls &&
    gModelEq x'' y'' && xis == yis
  gModelEq (Goal x xe xd)               (Goal y ye yd)      = x == y && xe == ye && xd == yd
  gModelEq (Soft x xe xd)               (Soft y ye yd)      = x == y && xe == ye && xd == yd
  gModelEq (Task x xe xd)               (Task y ye yd)      = x == y && xe == ye && xd == yd
  gModelEq (Res  x xe xd)               (Res  y ye yd)      = x == y && xe == ye && xd == yd
  gModelEq (Impacts xc xa xb)           (Impacts yc ya yb)  = xc == yc && xa == ya && xb == yb
  gModelEq (Effects xc xa xb)           (Effects yc ya yb)  = xc == yc && xa == ya && xb == yb
  gModelEq (AND x xs)                   (AND y ys)          = x == y && xs == ys
  gModelEq (XOR x xs)                   (XOR y ys)          = x == y && xs == ys
  gModelEq (IOR x xs)                   (IOR y ys)          = x == y && xs == ys
  gModelEq _                            _                   = False

  instance Eq (GModel ty) where
    (==) = gModelEq

-- ------------------------------------------------------ [ Decidable Equality ]

instance DecEq (GModel ty) where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void

-- ------------------------------------------------------------- [ Combinators ]

-- ------------------------------------------------------- [ Element Insertion ]
-- This section details the combinator for element insertion.
--
-- Correctness/Soundness Properties ::
--
-- 1. All elements added to the model must be unique.
--
-- Note ::
--
-- + This property should probably be replaced within the model using a Set.

data IsNewElem : GModel ELEM -> GModel MODEL -> Type where
  ElemIsNew : IsNewElem e m

decIsNew : (e : GModel ELEM) -> (m : GModel MODEL) -> Dec (IsNewElem e m)
decIsNew e (GRLSpec es _ _)  with (List.isElem e es)
    | Yes prf   = No (believe_me)
    | No contra = Yes (ElemIsNew)

private
insertElem : (e : GModel ELEM)
          -> (m : GModel MODEL)
          -> (prf : IsNewElem e m)
          -> GModel MODEL
insertElem e (GRLSpec es is ss) prf = GRLSpec (e::es) is ss

infixl 4 /+/

(/+/) : (m : GModel MODEL)
    -> (e : GModel ELEM)
    -> {auto prf : IsNewElem e m}
    -> GModel MODEL
(/+/) g x {prf} = insertElem x g prf

-- ---------------------------------------------- [ Intentional Link Insertion ]
-- This section details the combinator for intentional link insertion.
--
-- Correctness/Soundness Properties of an Intentional Link
--
-- 1. The link should use elements that are in the model.
-- 2. The destination cannot have type: Resource
-- 3. The src and destination must not be the same.


private
insertILink : (l : GModel ILINK)
           -> (m : GModel MODEL)
           -> GModel MODEL
insertILink l m@(GRLSpec es is ss) = GRLSpec es (l::is) ss

infixl 4 /+>/

(/+>/) : (m : GModel MODEL)
           -> (l : GModel ILINK)
           -> GModel MODEL
(/+>/) m l = insertILink l m

-- ----------------------------------------------- [ Structural Link Insertion ]
-- This section details the combinator for structural link insertion.
--
-- Correctness/Soundess Properties of a Structural Link
--
-- 1. A parent cannot be contained by its children.
-- 2. A node can only be decomposed once.
-- 3. The src and destination must not be the same.

private
insertSLink : (s : GModel SLINK)
           -> (m : GModel MODEL)
           -> GModel MODEL
insertSLink s m@(GRLSpec es is ss) = GRLSpec es is (s::ss)

infixl 4 /+</

(/+</) : (m : GModel MODEL)
          -> (s : GModel SLINK)
          -> (GModel MODEL)
(/+</) m s = insertSLink s m

-- ---------------------------------------------------------- [ Combine Models ]
-- private
-- insertModel : GModel MODEL
--            -> GModel MODEL
--            -> GModel MODEL
-- insertModel (GRLSpec xs ys zs) g =
--   let g'  = foldr (\e, m => insertElem e m) g xs   in
--   let g'' = foldr (insertILink) g' ys in
--       foldr insertSLink g'' zs


-- --------------------------------------------------------------------- [ EOF ]
